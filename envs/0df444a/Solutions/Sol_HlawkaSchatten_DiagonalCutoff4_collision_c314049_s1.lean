-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c314049_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:46:05.677759+00:00
-- url     : https://prove2.me/submissions/c1976ff9-897f-4809-b74f-7843c7fbe863

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
theorem collision_support_c314049_s1_s1_1 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (143420713/500000000 : ℝ)*x 0 + (-573694051/2000000000 : ℝ)*x 1 + (6582611511/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (143420713/500000000 : ℝ)^19 ≤ (20559523216709/100000000000000 : ℝ)^15 := by
    have hnat : (143420713 : ℕ)^19*100000000000000^15 ≤ 20559523216709^15*500000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      143420713 500000000 20559523216709 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (573694051/2000000000 : ℝ)^19 ≤ (64250098723/312500000000 : ℝ)^15 := by
    have hnat : (573694051 : ℕ)^19*312500000000^15 ≤ 64250098723^15*2000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      573694051 2000000000 64250098723 312500000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6582611511/10000000000 : ℝ)^19 ≤ (11776089034147/20000000000000 : ℝ)^15 := by
    have hnat : (6582611511 : ℕ)^19*20000000000000^15 ≤ 11776089034147^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6582611511 10000000000 11776089034147 20000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(143420713/500000000 : ℝ), (-573694051/2000000000 : ℝ), (6582611511/10000000000 : ℝ)] ![(20559523216709/100000000000000 : ℝ), (64250098723/312500000000 : ℝ), (11776089034147/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(143420713/500000000 : ℝ)|^19 ≤ (20559523216709/100000000000000 : ℝ)^15
        have hw : |(143420713/500000000 : ℝ)|=(143420713/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-573694051/2000000000 : ℝ)|^19 ≤ (64250098723/312500000000 : ℝ)^15
        have hw : |(-573694051/2000000000 : ℝ)|=(573694051/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6582611511/10000000000 : ℝ)|^19 ≤ (11776089034147/20000000000000 : ℝ)^15
        have hw : |(6582611511/10000000000 : ℝ)|=(6582611511/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314049_s1_s1_2 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (5413375057/10000000000 : ℝ)*x 0 + (5413284159/10000000000 : ℝ)*x 1 + (-1372003993/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5413375057/10000000000 : ℝ)^19 ≤ (45961368239789/100000000000000 : ℝ)^15 := by
    have hnat : (5413375057 : ℕ)^19*100000000000000^15 ≤ 45961368239789^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5413375057 10000000000 45961368239789 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5413284159/10000000000 : ℝ)^19 ≤ (45960390686303/100000000000000 : ℝ)^15 := by
    have hnat : (5413284159 : ℕ)^19*100000000000000^15 ≤ 45960390686303^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5413284159 10000000000 45960390686303 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1372003993/10000000000 : ℝ)^19 ≤ (1009780132679/12500000000000 : ℝ)^15 := by
    have hnat : (1372003993 : ℕ)^19*12500000000000^15 ≤ 1009780132679^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1372003993 10000000000 1009780132679 12500000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5413375057/10000000000 : ℝ), (5413284159/10000000000 : ℝ), (-1372003993/10000000000 : ℝ)] ![(45961368239789/100000000000000 : ℝ), (45960390686303/100000000000000 : ℝ), (1009780132679/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5413375057/10000000000 : ℝ)|^19 ≤ (45961368239789/100000000000000 : ℝ)^15
        have hw : |(5413375057/10000000000 : ℝ)|=(5413375057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5413284159/10000000000 : ℝ)|^19 ≤ (45960390686303/100000000000000 : ℝ)^15
        have hw : |(5413284159/10000000000 : ℝ)|=(5413284159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1372003993/10000000000 : ℝ)|^19 ≤ (1009780132679/12500000000000 : ℝ)^15
        have hw : |(-1372003993/10000000000 : ℝ)|=(1372003993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314049_s1_s1_6 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (514577887/1000000000 : ℝ)*x 0 + (1029138493/2000000000 : ℝ)*x 1 + (41867247/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (514577887/1000000000 : ℝ)^19 ≤ (10775681833777/25000000000000 : ℝ)^15 := by
    have hnat : (514577887 : ℕ)^19*25000000000000^15 ≤ 10775681833777^15*1000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      514577887 1000000000 10775681833777 25000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1029138493/2000000000 : ℝ)^19 ≤ (8620362115773/20000000000000 : ℝ)^15 := by
    have hnat : (1029138493 : ℕ)^19*20000000000000^15 ≤ 8620362115773^15*2000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1029138493 2000000000 8620362115773 20000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (41867247/200000000 : ℝ)^19 ≤ (3448865516283/25000000000000 : ℝ)^15 := by
    have hnat : (41867247 : ℕ)^19*25000000000000^15 ≤ 3448865516283^15*200000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41867247 200000000 3448865516283 25000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(514577887/1000000000 : ℝ), (1029138493/2000000000 : ℝ), (41867247/200000000 : ℝ)] ![(10775681833777/25000000000000 : ℝ), (8620362115773/20000000000000 : ℝ), (3448865516283/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(514577887/1000000000 : ℝ)|^19 ≤ (10775681833777/25000000000000 : ℝ)^15
        have hw : |(514577887/1000000000 : ℝ)|=(514577887/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1029138493/2000000000 : ℝ)|^19 ≤ (8620362115773/20000000000000 : ℝ)^15
        have hw : |(1029138493/2000000000 : ℝ)|=(1029138493/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(41867247/200000000 : ℝ)|^19 ≤ (3448865516283/25000000000000 : ℝ)^15
        have hw : |(41867247/200000000 : ℝ)|=(41867247/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314049_s1_s1_7 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-3466389993/10000000000 : ℝ)*x 0 + (3109895693/10000000000 : ℝ)*x 1 + (2942523239/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3466389993/10000000000 : ℝ)^19 ≤ (26132326051571/100000000000000 : ℝ)^15 := by
    have hnat : (3466389993 : ℕ)^19*100000000000000^15 ≤ 26132326051571^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3466389993 10000000000 26132326051571 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3109895693/10000000000 : ℝ)^19 ≤ (911041233847/4000000000000 : ℝ)^15 := by
    have hnat : (3109895693 : ℕ)^19*4000000000000^15 ≤ 911041233847^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3109895693 10000000000 911041233847 4000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2942523239/5000000000 : ℝ)^19 ≤ (51091643088139/100000000000000 : ℝ)^15 := by
    have hnat : (2942523239 : ℕ)^19*100000000000000^15 ≤ 51091643088139^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2942523239 5000000000 51091643088139 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3466389993/10000000000 : ℝ), (3109895693/10000000000 : ℝ), (2942523239/5000000000 : ℝ)] ![(26132326051571/100000000000000 : ℝ), (911041233847/4000000000000 : ℝ), (51091643088139/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3466389993/10000000000 : ℝ)|^19 ≤ (26132326051571/100000000000000 : ℝ)^15
        have hw : |(-3466389993/10000000000 : ℝ)|=(3466389993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3109895693/10000000000 : ℝ)|^19 ≤ (911041233847/4000000000000 : ℝ)^15
        have hw : |(3109895693/10000000000 : ℝ)|=(3109895693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2942523239/5000000000 : ℝ)|^19 ≤ (51091643088139/100000000000000 : ℝ)^15
        have hw : |(2942523239/5000000000 : ℝ)|=(2942523239/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314049_s1_s1_8 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (683242511/2500000000 : ℝ)*x 0 + (-2451902927/10000000000 : ℝ)*x 1 + (7013835533/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (683242511/2500000000 : ℝ)^19 ≤ (4834417787357/25000000000000 : ℝ)^15 := by
    have hnat : (683242511 : ℕ)^19*25000000000000^15 ≤ 4834417787357^15*2500000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      683242511 2500000000 4834417787357 25000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2451902927/10000000000 : ℝ)^19 ≤ (16854044825201/100000000000000 : ℝ)^15 := by
    have hnat : (2451902927 : ℕ)^19*100000000000000^15 ≤ 16854044825201^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2451902927 10000000000 16854044825201 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7013835533/10000000000 : ℝ)^19 ≤ (7976035501719/12500000000000 : ℝ)^15 := by
    have hnat : (7013835533 : ℕ)^19*12500000000000^15 ≤ 7976035501719^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7013835533 10000000000 7976035501719 12500000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(683242511/2500000000 : ℝ), (-2451902927/10000000000 : ℝ), (7013835533/10000000000 : ℝ)] ![(4834417787357/25000000000000 : ℝ), (16854044825201/100000000000000 : ℝ), (7976035501719/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(683242511/2500000000 : ℝ)|^19 ≤ (4834417787357/25000000000000 : ℝ)^15
        have hw : |(683242511/2500000000 : ℝ)|=(683242511/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2451902927/10000000000 : ℝ)|^19 ≤ (16854044825201/100000000000000 : ℝ)^15
        have hw : |(-2451902927/10000000000 : ℝ)|=(2451902927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(7013835533/10000000000 : ℝ)|^19 ≤ (7976035501719/12500000000000 : ℝ)^15
        have hw : |(7013835533/10000000000 : ℝ)|=(7013835533/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314049_s1_s1_9 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (2564458827/5000000000 : ℝ)*x 0 + (243574463/400000000 : ℝ)*x 1 + (-93125261/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2564458827/5000000000 : ℝ)^19 ≤ (42923907812511/100000000000000 : ℝ)^15 := by
    have hnat : (2564458827 : ℕ)^19*100000000000000^15 ≤ 42923907812511^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2564458827 5000000000 42923907812511 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (243574463/400000000 : ℝ)^19 ≤ (6668593509787/12500000000000 : ℝ)^15 := by
    have hnat : (243574463 : ℕ)^19*12500000000000^15 ≤ 6668593509787^15*400000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      243574463 400000000 6668593509787 12500000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (93125261/1250000000 : ℝ)^19 ≤ (3727344096241/100000000000000 : ℝ)^15 := by
    have hnat : (93125261 : ℕ)^19*100000000000000^15 ≤ 3727344096241^15*1250000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      93125261 1250000000 3727344096241 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2564458827/5000000000 : ℝ), (243574463/400000000 : ℝ), (-93125261/1250000000 : ℝ)] ![(42923907812511/100000000000000 : ℝ), (6668593509787/12500000000000 : ℝ), (3727344096241/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2564458827/5000000000 : ℝ)|^19 ≤ (42923907812511/100000000000000 : ℝ)^15
        have hw : |(2564458827/5000000000 : ℝ)|=(2564458827/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(243574463/400000000 : ℝ)|^19 ≤ (6668593509787/12500000000000 : ℝ)^15
        have hw : |(243574463/400000000 : ℝ)|=(243574463/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-93125261/1250000000 : ℝ)|^19 ≤ (3727344096241/100000000000000 : ℝ)^15
        have hw : |(-93125261/1250000000 : ℝ)|=(93125261/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314049_s1_s1_12 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (5027447893/10000000000 : ℝ)*x 0 + (1492222633/2500000000 : ℝ)*x 1 + (110389451/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5027447893/10000000000 : ℝ)^19 ≤ (20925552643509/50000000000000 : ℝ)^15 := by
    have hnat : (5027447893 : ℕ)^19*50000000000000^15 ≤ 20925552643509^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5027447893 10000000000 20925552643509 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1492222633/2500000000 : ℝ)^19 ≤ (1040307924859/2000000000000 : ℝ)^15 := by
    have hnat : (1492222633 : ℕ)^19*2000000000000^15 ≤ 1040307924859^15*2500000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1492222633 2500000000 1040307924859 2000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (110389451/1000000000 : ℝ)^19 ≤ (6133498448179/100000000000000 : ℝ)^15 := by
    have hnat : (110389451 : ℕ)^19*100000000000000^15 ≤ 6133498448179^15*1000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      110389451 1000000000 6133498448179 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5027447893/10000000000 : ℝ), (1492222633/2500000000 : ℝ), (110389451/1000000000 : ℝ)] ![(20925552643509/50000000000000 : ℝ), (1040307924859/2000000000000 : ℝ), (6133498448179/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5027447893/10000000000 : ℝ)|^19 ≤ (20925552643509/50000000000000 : ℝ)^15
        have hw : |(5027447893/10000000000 : ℝ)|=(5027447893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1492222633/2500000000 : ℝ)|^19 ≤ (1040307924859/2000000000000 : ℝ)^15
        have hw : |(1492222633/2500000000 : ℝ)|=(1492222633/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(110389451/1000000000 : ℝ)|^19 ≤ (6133498448179/100000000000000 : ℝ)^15
        have hw : |(110389451/1000000000 : ℝ)|=(110389451/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314049_s1_s1_13 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-3109828301/10000000000 : ℝ)*x 0 + (433307323/1250000000 : ℝ)*x 1 + (5885043767/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3109828301/10000000000 : ℝ)^19 ≤ (355865713611/1562500000000 : ℝ)^15 := by
    have hnat : (3109828301 : ℕ)^19*1562500000000^15 ≤ 355865713611^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3109828301 10000000000 355865713611 1562500000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (433307323/1250000000 : ℝ)^19 ≤ (26132981036441/100000000000000 : ℝ)^15 := by
    have hnat : (433307323 : ℕ)^19*100000000000000^15 ≤ 26132981036441^15*1250000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      433307323 1250000000 26132981036441 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5885043767/10000000000 : ℝ)^19 ≤ (12772903319023/25000000000000 : ℝ)^15 := by
    have hnat : (5885043767 : ℕ)^19*25000000000000^15 ≤ 12772903319023^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5885043767 10000000000 12772903319023 25000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3109828301/10000000000 : ℝ), (433307323/1250000000 : ℝ), (5885043767/10000000000 : ℝ)] ![(355865713611/1562500000000 : ℝ), (26132981036441/100000000000000 : ℝ), (12772903319023/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3109828301/10000000000 : ℝ)|^19 ≤ (355865713611/1562500000000 : ℝ)^15
        have hw : |(-3109828301/10000000000 : ℝ)|=(3109828301/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(433307323/1250000000 : ℝ)|^19 ≤ (26132981036441/100000000000000 : ℝ)^15
        have hw : |(433307323/1250000000 : ℝ)|=(433307323/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5885043767/10000000000 : ℝ)|^19 ≤ (12772903319023/25000000000000 : ℝ)^15
        have hw : |(5885043767/10000000000 : ℝ)|=(5885043767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314049_s1_s1_14 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (2451848663/10000000000 : ℝ)*x 0 + (-1366511431/5000000000 : ℝ)*x 1 + (7013835453/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2451848663/10000000000 : ℝ)^19 ≤ (3370714471149/20000000000000 : ℝ)^15 := by
    have hnat : (2451848663 : ℕ)^19*20000000000000^15 ≤ 3370714471149^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2451848663 10000000000 3370714471149 20000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1366511431/5000000000 : ℝ)^19 ≤ (19338144534667/100000000000000 : ℝ)^15 := by
    have hnat : (1366511431 : ℕ)^19*100000000000000^15 ≤ 19338144534667^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1366511431 5000000000 19338144534667 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7013835453/10000000000 : ℝ)^19 ≤ (63808283091873/100000000000000 : ℝ)^15 := by
    have hnat : (7013835453 : ℕ)^19*100000000000000^15 ≤ 63808283091873^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7013835453 10000000000 63808283091873 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2451848663/10000000000 : ℝ), (-1366511431/5000000000 : ℝ), (7013835453/10000000000 : ℝ)] ![(3370714471149/20000000000000 : ℝ), (19338144534667/100000000000000 : ℝ), (63808283091873/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2451848663/10000000000 : ℝ)|^19 ≤ (3370714471149/20000000000000 : ℝ)^15
        have hw : |(2451848663/10000000000 : ℝ)|=(2451848663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1366511431/5000000000 : ℝ)|^19 ≤ (19338144534667/100000000000000 : ℝ)^15
        have hw : |(-1366511431/5000000000 : ℝ)|=(1366511431/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(7013835453/10000000000 : ℝ)|^19 ≤ (63808283091873/100000000000000 : ℝ)^15
        have hw : |(7013835453/10000000000 : ℝ)|=(7013835453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314049_s1_s1_15 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (761181451/1250000000 : ℝ)*x 0 + (5128823823/10000000000 : ℝ)*x 1 + (-372500693/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (761181451/1250000000 : ℝ)^19 ≤ (53349747197691/100000000000000 : ℝ)^15 := by
    have hnat : (761181451 : ℕ)^19*100000000000000^15 ≤ 53349747197691^15*1250000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      761181451 1250000000 53349747197691 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5128823823/10000000000 : ℝ)^19 ≤ (42922913137621/100000000000000 : ℝ)^15 := by
    have hnat : (5128823823 : ℕ)^19*100000000000000^15 ≤ 42922913137621^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5128823823 10000000000 42922913137621 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (372500693/5000000000 : ℝ)^19 ≤ (116479363983/3125000000000 : ℝ)^15 := by
    have hnat : (372500693 : ℕ)^19*3125000000000^15 ≤ 116479363983^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      372500693 5000000000 116479363983 3125000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(761181451/1250000000 : ℝ), (5128823823/10000000000 : ℝ), (-372500693/5000000000 : ℝ)] ![(53349747197691/100000000000000 : ℝ), (42922913137621/100000000000000 : ℝ), (116479363983/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(761181451/1250000000 : ℝ)|^19 ≤ (53349747197691/100000000000000 : ℝ)^15
        have hw : |(761181451/1250000000 : ℝ)|=(761181451/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5128823823/10000000000 : ℝ)|^19 ≤ (42922913137621/100000000000000 : ℝ)^15
        have hw : |(5128823823/10000000000 : ℝ)|=(5128823823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-372500693/5000000000 : ℝ)|^19 ≤ (116479363983/3125000000000 : ℝ)^15
        have hw : |(-372500693/5000000000 : ℝ)|=(372500693/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314049_s1_s1_18 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (5968978591/10000000000 : ℝ)*x 0 + (5027355757/10000000000 : ℝ)*x 1 + (27597361/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5968978591/10000000000 : ℝ)^19 ≤ (52016368263043/100000000000000 : ℝ)^15 := by
    have hnat : (5968978591 : ℕ)^19*100000000000000^15 ≤ 52016368263043^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5968978591 10000000000 52016368263043 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5027355757/10000000000 : ℝ)^19 ≤ (10462533442737/25000000000000 : ℝ)^15 := by
    have hnat : (5027355757 : ℕ)^19*25000000000000^15 ≤ 10462533442737^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5027355757 10000000000 10462533442737 25000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (27597361/250000000 : ℝ)^19 ≤ (3066748977763/50000000000000 : ℝ)^15 := by
    have hnat : (27597361 : ℕ)^19*50000000000000^15 ≤ 3066748977763^15*250000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      27597361 250000000 3066748977763 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5968978591/10000000000 : ℝ), (5027355757/10000000000 : ℝ), (27597361/250000000 : ℝ)] ![(52016368263043/100000000000000 : ℝ), (10462533442737/25000000000000 : ℝ), (3066748977763/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5968978591/10000000000 : ℝ)|^19 ≤ (52016368263043/100000000000000 : ℝ)^15
        have hw : |(5968978591/10000000000 : ℝ)|=(5968978591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5027355757/10000000000 : ℝ)|^19 ≤ (10462533442737/25000000000000 : ℝ)^15
        have hw : |(5027355757/10000000000 : ℝ)|=(5027355757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(27597361/250000000 : ℝ)|^19 ≤ (3066748977763/50000000000000 : ℝ)^15
        have hw : |(27597361/250000000 : ℝ)|=(27597361/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314049_s1_s1_19 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-408910623/1000000000 : ℝ)*x 0 + (3668630829/10000000000 : ℝ)*x 1 + (2411460337/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (408910623/1000000000 : ℝ)^19 ≤ (6443066695539/20000000000000 : ℝ)^15 := by
    have hnat : (408910623 : ℕ)^19*20000000000000^15 ≤ 6443066695539^15*1000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      408910623 1000000000 6443066695539 20000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3668630829/10000000000 : ℝ)^19 ≤ (28078360627101/100000000000000 : ℝ)^15 := by
    have hnat : (3668630829 : ℕ)^19*100000000000000^15 ≤ 28078360627101^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3668630829 10000000000 28078360627101 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2411460337/5000000000 : ℝ)^19 ≤ (9926576469447/25000000000000 : ℝ)^15 := by
    have hnat : (2411460337 : ℕ)^19*25000000000000^15 ≤ 9926576469447^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2411460337 5000000000 9926576469447 25000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-408910623/1000000000 : ℝ), (3668630829/10000000000 : ℝ), (2411460337/5000000000 : ℝ)] ![(6443066695539/20000000000000 : ℝ), (28078360627101/100000000000000 : ℝ), (9926576469447/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-408910623/1000000000 : ℝ)|^19 ≤ (6443066695539/20000000000000 : ℝ)^15
        have hw : |(-408910623/1000000000 : ℝ)|=(408910623/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3668630829/10000000000 : ℝ)|^19 ≤ (28078360627101/100000000000000 : ℝ)^15
        have hw : |(3668630829/10000000000 : ℝ)|=(3668630829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2411460337/5000000000 : ℝ)|^19 ≤ (9926576469447/25000000000000 : ℝ)^15
        have hw : |(2411460337/5000000000 : ℝ)|=(2411460337/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314049_s1_s1_20 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (2464504591/10000000000 : ℝ)*x 0 + (-2885106951/10000000000 : ℝ)*x 1 + (3442398157/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2464504591/10000000000 : ℝ)^19 ≤ (4240960315457/25000000000000 : ℝ)^15 := by
    have hnat : (2464504591 : ℕ)^19*25000000000000^15 ≤ 4240960315457^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2464504591 10000000000 4240960315457 25000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2885106951/10000000000 : ℝ)^19 ≤ (20711192011719/100000000000000 : ℝ)^15 := by
    have hnat : (2885106951 : ℕ)^19*100000000000000^15 ≤ 20711192011719^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2885106951 10000000000 20711192011719 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3442398157/5000000000 : ℝ)^19 ≤ (15581241678021/25000000000000 : ℝ)^15 := by
    have hnat : (3442398157 : ℕ)^19*25000000000000^15 ≤ 15581241678021^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3442398157 5000000000 15581241678021 25000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2464504591/10000000000 : ℝ), (-2885106951/10000000000 : ℝ), (3442398157/5000000000 : ℝ)] ![(4240960315457/25000000000000 : ℝ), (20711192011719/100000000000000 : ℝ), (15581241678021/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2464504591/10000000000 : ℝ)|^19 ≤ (4240960315457/25000000000000 : ℝ)^15
        have hw : |(2464504591/10000000000 : ℝ)|=(2464504591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2885106951/10000000000 : ℝ)|^19 ≤ (20711192011719/100000000000000 : ℝ)^15
        have hw : |(-2885106951/10000000000 : ℝ)|=(2885106951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3442398157/5000000000 : ℝ)|^19 ≤ (15581241678021/25000000000000 : ℝ)^15
        have hw : |(3442398157/5000000000 : ℝ)|=(3442398157/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314049_s1_s1_21 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1366617213/2500000000 : ℝ)*x 0 + (5350654497/10000000000 : ℝ)*x 1 + (-692748503/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1366617213/2500000000 : ℝ)^19 ≤ (46533106363167/100000000000000 : ℝ)^15 := by
    have hnat : (1366617213 : ℕ)^19*100000000000000^15 ≤ 46533106363167^15*2500000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1366617213 2500000000 46533106363167 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5350654497/10000000000 : ℝ)^19 ≤ (9057577941071/20000000000000 : ℝ)^15 := by
    have hnat : (5350654497 : ℕ)^19*20000000000000^15 ≤ 9057577941071^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5350654497 10000000000 9057577941071 20000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (692748503/5000000000 : ℝ)^19 ≤ (4089501957397/50000000000000 : ℝ)^15 := by
    have hnat : (692748503 : ℕ)^19*50000000000000^15 ≤ 4089501957397^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      692748503 5000000000 4089501957397 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1366617213/2500000000 : ℝ), (5350654497/10000000000 : ℝ), (-692748503/5000000000 : ℝ)] ![(46533106363167/100000000000000 : ℝ), (9057577941071/20000000000000 : ℝ), (4089501957397/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1366617213/2500000000 : ℝ)|^19 ≤ (46533106363167/100000000000000 : ℝ)^15
        have hw : |(1366617213/2500000000 : ℝ)|=(1366617213/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5350654497/10000000000 : ℝ)|^19 ≤ (9057577941071/20000000000000 : ℝ)^15
        have hw : |(5350654497/10000000000 : ℝ)|=(5350654497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-692748503/5000000000 : ℝ)|^19 ≤ (4089501957397/50000000000000 : ℝ)^15
        have hw : |(-692748503/5000000000 : ℝ)|=(692748503/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314049_s1_s1_25 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1147842683/2500000000 : ℝ)*x 0 + (5350654497/10000000000 : ℝ)*x 1 + (2514945993/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1147842683/2500000000 : ℝ)^19 ≤ (37307286116527/100000000000000 : ℝ)^15 := by
    have hnat : (1147842683 : ℕ)^19*100000000000000^15 ≤ 37307286116527^15*2500000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1147842683 2500000000 37307286116527 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5350654497/10000000000 : ℝ)^19 ≤ (9057577941071/20000000000000 : ℝ)^15 := by
    have hnat : (5350654497 : ℕ)^19*20000000000000^15 ≤ 9057577941071^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5350654497 10000000000 9057577941071 20000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2514945993/10000000000 : ℝ)^19 ≤ (17404824166199/100000000000000 : ℝ)^15 := by
    have hnat : (2514945993 : ℕ)^19*100000000000000^15 ≤ 17404824166199^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2514945993 10000000000 17404824166199 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1147842683/2500000000 : ℝ), (5350654497/10000000000 : ℝ), (2514945993/10000000000 : ℝ)] ![(37307286116527/100000000000000 : ℝ), (9057577941071/20000000000000 : ℝ), (17404824166199/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1147842683/2500000000 : ℝ)|^19 ≤ (37307286116527/100000000000000 : ℝ)^15
        have hw : |(1147842683/2500000000 : ℝ)|=(1147842683/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5350654497/10000000000 : ℝ)|^19 ≤ (9057577941071/20000000000000 : ℝ)^15
        have hw : |(5350654497/10000000000 : ℝ)|=(5350654497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2514945993/10000000000 : ℝ)|^19 ≤ (17404824166199/100000000000000 : ℝ)^15
        have hw : |(2514945993/10000000000 : ℝ)|=(2514945993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c314049_s1 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (172069/100000 : ℝ) (87867/50000 : ℝ) (15771/20000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, false, true]])
    (hprev0 : (0 : ℝ) ≤ ((75257/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(75257/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(75263/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(75263/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(4373/25000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(4373/25000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((17857/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(17857/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(17857/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(17857/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(1509/50000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(1509/50000 : ℝ)*X 1 2) := by
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
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (15771/20000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (15771/20000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base5 : ((1 : ℝ)*N 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 2]
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base59 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.1]
  have base60 : ((1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 1+(1 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
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
  have s1_pow0 : (75257/100000 : ℝ) ^ (37/8 : ℝ) ≤ (13427631848873313469/50000000000000000000 : ℝ) := by
    have hpowers : (75257/100000 : ℝ)^37 ≤ (13427631848873313469/50000000000000000000 : ℝ)^8 := by
      have hnat : (75257 : ℕ)^37*50000000000000000000^8 ≤ 13427631848873313469^8*100000^37 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        75257 100000 13427631848873313469 50000000000000000000 37 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (75257/100000 : ℝ)) (X := (13427631848873313469/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s1_corner0a : (63427631848873313469/50000000000000000000 : ℝ) ≤ (526389206611213/500000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (63427631848873313469/50000000000000000000 : ℝ)^8 ≤ (526389206611213/500000000000000 : ℝ)^37 := by
      have hnat : (63427631848873313469 : ℕ)^8*500000000000000^37 ≤ 526389206611213^37*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        63427631848873313469 50000000000000000000 526389206611213 500000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (526389206611213/500000000000000 : ℝ)) (X := (63427631848873313469/50000000000000000000 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s1_corner0b : (38427631848873313469/25000000000000000000 : ℝ) ≤ (685880358262163/625000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (38427631848873313469/25000000000000000000 : ℝ)^8 ≤ (685880358262163/625000000000000 : ℝ)^37 := by
      have hnat : (38427631848873313469 : ℕ)^8*625000000000000^37 ≤ 685880358262163^37*25000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        38427631848873313469 25000000000000000000 685880358262163 625000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (685880358262163/625000000000000 : ℝ)) (X := (38427631848873313469/25000000000000000000 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(26389206611213/376285000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(111575399992587/1881425000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (37/8 : ℝ)) (rho := (75257/100000 : ℝ)) (alpha := (26389206611213/376285000000000 : ℝ)) (beta := (111575399992587/1881425000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (75257/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(26389206611213/376285000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(111575399992587/1881425000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (75263/100000 : ℝ) ^ (37/8 : ℝ) ≤ (6716291910939491497/25000000000000000000 : ℝ) := by
    have hpowers : (75263/100000 : ℝ)^37 ≤ (6716291910939491497/25000000000000000000 : ℝ)^8 := by
      have hnat : (75263 : ℕ)^37*25000000000000000000^8 ≤ 6716291910939491497^8*100000^37 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        75263 100000 6716291910939491497 25000000000000000000 37 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (75263/100000 : ℝ)) (X := (6716291910939491497/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s1_corner1a : (31716291910939491497/25000000000000000000 : ℝ) ≤ (5263980921081829/5000000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (31716291910939491497/25000000000000000000 : ℝ)^8 ≤ (5263980921081829/5000000000000000 : ℝ)^37 := by
      have hnat : (31716291910939491497 : ℕ)^8*5000000000000000^37 ≤ 5263980921081829^37*25000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        31716291910939491497 25000000000000000000 5263980921081829 5000000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5263980921081829/5000000000000000 : ℝ)) (X := (31716291910939491497/25000000000000000000 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s1_corner1b : (19216291910939491497/12500000000000000000 : ℝ) ≤ (2743597871052361/2500000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (19216291910939491497/12500000000000000000 : ℝ)^8 ≤ (2743597871052361/2500000000000000 : ℝ)^37 := by
      have hnat : (19216291910939491497 : ℕ)^8*2500000000000000^37 ≤ 2743597871052361^37*12500000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        19216291910939491497 12500000000000000000 2743597871052361 2500000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2743597871052361/2500000000000000 : ℝ)) (X := (19216291910939491497/12500000000000000000 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(263980921081829/3763150000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(223214821022893/3763150000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (37/8 : ℝ)) (rho := (75263/100000 : ℝ)) (alpha := (263980921081829/3763150000000000 : ℝ)) (beta := (223214821022893/3763150000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (75263/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(263980921081829/3763150000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(223214821022893/3763150000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (4373/25000 : ℝ) ^ (37/8 : ℝ) ≤ (393588640504761/1250000000000000000 : ℝ) := by
    have hpowers : (4373/25000 : ℝ)^37 ≤ (393588640504761/1250000000000000000 : ℝ)^8 := by
      have hnat : (4373 : ℕ)^37*1250000000000000000^8 ≤ 393588640504761^8*25000^37 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4373 25000 393588640504761 1250000000000000000 37 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4373/25000 : ℝ)) (X := (393588640504761/1250000000000000000 : ℝ)) (by norm_num) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s1_corner2a : (1250393588640504761/1250000000000000000 : ℝ) ≤ (10000680717980687/10000000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (1250393588640504761/1250000000000000000 : ℝ)^8 ≤ (10000680717980687/10000000000000000 : ℝ)^37 := by
      have hnat : (1250393588640504761 : ℕ)^8*10000000000000000^37 ≤ 10000680717980687^37*1250000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1250393588640504761 1250000000000000000 10000680717980687 10000000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000680717980687/10000000000000000 : ℝ)) (X := (1250393588640504761/1250000000000000000 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s1_corner2b : (625393588640504761/625000000000000000 : ℝ) ≤ (1250170158505011/1250000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (625393588640504761/625000000000000000 : ℝ)^8 ≤ (1250170158505011/1250000000000000 : ℝ)^37 := by
      have hnat : (625393588640504761 : ℕ)^8*1250000000000000^37 ≤ 1250170158505011^37*625000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        625393588640504761 625000000000000000 1250170158505011 1250000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250170158505011/1250000000000000 : ℝ)) (X := (625393588640504761/625000000000000000 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(680717980687/1749200000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(680550059401/1749200000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (37/8 : ℝ)) (rho := (4373/25000 : ℝ)) (alpha := (680717980687/1749200000000000 : ℝ)) (beta := (680550059401/1749200000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, false, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (4373/25000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(680717980687/1749200000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(680550059401/1749200000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_1 : ((143420713/500000000 : ℝ)*X 1 0+(-573694051/2000000000 : ℝ)*X 1 1+(6582611511/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c314049_s1_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((5413375057/10000000000 : ℝ)*X 2 0+(5413284159/10000000000 : ℝ)*X 2 1+(-1372003993/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c314049_s1_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((514577887/1000000000 : ℝ)*X 0 0+(1029138493/2000000000 : ℝ)*X 0 1+(41867247/200000000 : ℝ)*X 0 2+(514577887/1000000000 : ℝ)*X 1 0+(1029138493/2000000000 : ℝ)*X 1 1+(41867247/200000000 : ℝ)*X 1 2+(514577887/1000000000 : ℝ)*X 2 0+(1029138493/2000000000 : ℝ)*X 2 1+(41867247/200000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c314049_s1_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-3466389993/10000000000 : ℝ)*X 0 0+(3109895693/10000000000 : ℝ)*X 0 1+(2942523239/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c314049_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((683242511/2500000000 : ℝ)*X 1 0+(-2451902927/10000000000 : ℝ)*X 1 1+(7013835533/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c314049_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((2564458827/5000000000 : ℝ)*X 2 0+(243574463/400000000 : ℝ)*X 2 1+(-93125261/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c314049_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_12 : ((5027447893/10000000000 : ℝ)*X 0 0+(1492222633/2500000000 : ℝ)*X 0 1+(110389451/1000000000 : ℝ)*X 0 2+(5027447893/10000000000 : ℝ)*X 1 0+(1492222633/2500000000 : ℝ)*X 1 1+(110389451/1000000000 : ℝ)*X 1 2+(5027447893/10000000000 : ℝ)*X 2 0+(1492222633/2500000000 : ℝ)*X 2 1+(110389451/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c314049_s1_s1_12 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((-3109828301/10000000000 : ℝ)*X 0 0+(433307323/1250000000 : ℝ)*X 0 1+(5885043767/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c314049_s1_s1_13 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((2451848663/10000000000 : ℝ)*X 1 0+(-1366511431/5000000000 : ℝ)*X 1 1+(7013835453/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c314049_s1_s1_14 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((761181451/1250000000 : ℝ)*X 2 0+(5128823823/10000000000 : ℝ)*X 2 1+(-372500693/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c314049_s1_s1_15 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_18 : ((5968978591/10000000000 : ℝ)*X 0 0+(5027355757/10000000000 : ℝ)*X 0 1+(27597361/250000000 : ℝ)*X 0 2+(5968978591/10000000000 : ℝ)*X 1 0+(5027355757/10000000000 : ℝ)*X 1 1+(27597361/250000000 : ℝ)*X 1 2+(5968978591/10000000000 : ℝ)*X 2 0+(5027355757/10000000000 : ℝ)*X 2 1+(27597361/250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c314049_s1_s1_18 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_19 : ((-408910623/1000000000 : ℝ)*X 0 0+(3668630829/10000000000 : ℝ)*X 0 1+(2411460337/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c314049_s1_s1_19 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((2464504591/10000000000 : ℝ)*X 1 0+(-2885106951/10000000000 : ℝ)*X 1 1+(3442398157/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c314049_s1_s1_20 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((1366617213/2500000000 : ℝ)*X 2 0+(5350654497/10000000000 : ℝ)*X 2 1+(-692748503/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c314049_s1_s1_21 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_25 : ((1147842683/2500000000 : ℝ)*X 0 0+(5350654497/10000000000 : ℝ)*X 0 1+(2514945993/10000000000 : ℝ)*X 0 2+(1147842683/2500000000 : ℝ)*X 1 0+(5350654497/10000000000 : ℝ)*X 1 1+(2514945993/10000000000 : ℝ)*X 1 2+(1147842683/2500000000 : ℝ)*X 2 0+(5350654497/10000000000 : ℝ)*X 2 1+(2514945993/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c314049_s1_s1_25 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((17857/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(17857/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (2514647360123541335886052981449/154806047346518750000000000000000000 : ℝ) := by norm_num
    linear_combination (3499007/1000000000000 : ℝ)*(base39) + (295126191161/1000000000000 : ℝ)*(base49) + (85421681619/25000000000 : ℝ)*(base59) + (191423843701/100000000000 : ℝ)*(base60) + (1776340870469/250000000000 : ℝ)*(major_s1_0) + (1776340870469/250000000000 : ℝ)*(major_s1_1) + (1776340870469/250000000000 : ℝ)*(major_s1_2) + (159692551/1000000000000 : ℝ)*(sp_s1_1) + (10081188538583/1000000000000 : ℝ)*(sp_s1_7) + (10081193125497/1000000000000 : ℝ)*(sp_s1_8) + (10081352818047/1000000000000 : ℝ)*(sp_s1_9) + (2064634183579/500000000000 : ℝ)*(sp_s1_12) + (20534933/125000000000 : ℝ)*(sp_s1_13) + (50181959/500000000000 : ℝ)*(sp_s1_25) + (1032342182769/250000000000 : ℝ)*(f.failure) + (10081352818047/1000000000000 : ℝ)*(f.sum) + (2610645261275186733/6582501980000000000000000000000 : ℝ)*base63 + (115626105113121/437300000000000000000000000 : ℝ)*base65 + (454334589076399/470393750000000000000000000 : ℝ)*base67 + (318485661159257/437300000000000000000000000 : ℝ)*base69 + (2628778201605800833/32909886100000000000000000000000 : ℝ)*base70 + (9165276869451/58794531250000000000000000 : ℝ)*base73 + (726258672390921/940787500000000000000000000 : ℝ)*base75 + (621973112675137/752570000000000000000000000 : ℝ)*base77 + (68590918159757511723/141601689775000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base83 + (20939/25000000000000000 : ℝ)*base86 + (20939/25000000000000000 : ℝ)*base88 + (20939/25000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(17857/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(17857/50000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (34838111053388493793746098268453/4953793515088600000000000000000000000 : ℝ) := by norm_num
    linear_combination (2410839/250000000000 : ℝ)*(base21) + (59027677911/200000000000 : ℝ)*(base49) + (417599289221/125000000000 : ℝ)*(base59) + (541495616251/250000000000 : ℝ)*(base60) + (7105334932181/1000000000000 : ℝ)*(major_s1_0) + (7105334932181/1000000000000 : ℝ)*(major_s1_1) + (7105334932181/1000000000000 : ℝ)*(major_s1_2) + (17509871/1000000000000 : ℝ)*(sp_s1_6) + (2461809/50000000000 : ℝ)*(sp_s1_8) + (5040657690541/500000000000 : ℝ)*(sp_s1_13) + (5040633072451/500000000000 : ℝ)*(sp_s1_14) + (2520304488757/250000000000 : ℝ)*(sp_s1_15) + (2064667314601/500000000000 : ℝ)*(sp_s1_18) + (43891349/500000000000 : ℝ)*(sp_s1_21) + (4129352139073/1000000000000 : ℝ)*(f.failure) + (5040657690541/500000000000 : ℝ)*(f.sum) + (19562654331049602249/26330007920000000000000000000000 : ℝ)*base62 + (148141261206779/1749200000000000000000000000 : ℝ)*base65 + (769302845075193/3763150000000000000000000000 : ℝ)*base66 + (1159900192090507/1749200000000000000000000000 : ℝ)*base68 + (407197634112923597/131639544400000000000000000000000 : ℝ)*base70 + (159934600024917/1881425000000000000000000000 : ℝ)*base73 + (118076129512631/3763150000000000000000000000 : ℝ)*base74 + (120363078893797/752570000000000000000000000 : ℝ)*base76 + (79494020935774417729/283203379550000000000000000000000 : ℝ)*base78 + (52037/100000000000000000 : ℝ)*base87 + (52037/100000000000000000 : ℝ)*base89 + (52037/100000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(1509/50000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(1509/50000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (23353224366972484812468707383701/2476896757544300000000000000000000000 : ℝ) := by norm_num
    linear_combination (299600857003/500000000000 : ℝ)*(base5) + (2170763/1000000000000 : ℝ)*(base40) + (32909716067/100000000000 : ℝ)*(base49) + (638748012497/1000000000000 : ℝ)*(base59) + (1892155993053/1000000000000 : ℝ)*(major_s1_0) + (1892155993053/1000000000000 : ℝ)*(major_s1_1) + (1892155993053/1000000000000 : ℝ)*(major_s1_2) + (5127613/100000000000 : ℝ)*(sp_s1_1) + (1082345373/1000000000000 : ℝ)*(sp_s1_2) + (2849929/20000000000 : ℝ)*(sp_s1_6) + (536931857629/200000000000 : ℝ)*(sp_s1_19) + (536921602403/200000000000 : ℝ)*(sp_s1_20) + (1641389328389/500000000000 : ℝ)*(sp_s1_21) + (100061068939/200000000000 : ℝ)*(sp_s1_25) + (1099649555151/1000000000000 : ℝ)*(f.failure) + (536931857629/200000000000 : ℝ)*(f.sum) + (188595374016953297/26330007920000000000000000000000 : ℝ)*base62 + (29322189598347/1749200000000000000000000000 : ℝ)*base65 + (39373670672163/470393750000000000000000000 : ℝ)*base66 + (95137538310011/1749200000000000000000000000 : ℝ)*base68 + (55790896844405616739/131639544400000000000000000000000 : ℝ)*base71 + (1758057266939653/3762850000000000000000000000 : ℝ)*base72 + (131640217509741/1881575000000000000000000000 : ℝ)*base75 + (77526056339903/188142500000000000000000000 : ℝ)*base77 + (134632867595335190157/283203379550000000000000000000000 : ℝ)*base78 + (22581/100000000000000000 : ℝ)*base86 + (22581/100000000000000000 : ℝ)*base88 + (22581/100000000000000000 : ℝ)*base90 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (172069/100000 : ℝ) (87867/50000 : ℝ) (15771/20000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, false, true]])
    (hprev0 : (0 : ℝ) ≤ ((75257/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(75257/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(75263/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(75263/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(4373/25000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(4373/25000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((17857/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(17857/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(17857/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(17857/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(1509/50000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(1509/50000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c314049_s1 p hpa hpb X hX hprev0

#print axioms solution
