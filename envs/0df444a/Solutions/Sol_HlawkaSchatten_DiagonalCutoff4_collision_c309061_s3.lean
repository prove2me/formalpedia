-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c309061_s3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:04:39.757991+00:00
-- url     : https://prove2.me/submissions/43cbe752-68f7-4eff-a9c2-41f497b41afc

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
theorem collision_support_c309061_s3_s3_0 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-3848779/19531250 : ℝ)*x 0 + (1142242877/2500000000 : ℝ)*x 1 + (6002062653/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3848779/19531250 : ℝ)^35 ≤ (12178209323053/100000000000000 : ℝ)^27 := by
    have hnat : (3848779 : ℕ)^35*100000000000000^27 ≤ 12178209323053^27*19531250^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3848779 19531250 12178209323053 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1142242877/2500000000 : ℝ)^35 ≤ (36226294754467/100000000000000 : ℝ)^27 := by
    have hnat : (1142242877 : ℕ)^35*100000000000000^27 ≤ 36226294754467^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1142242877 2500000000 36226294754467 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6002062653/10000000000 : ℝ)^35 ≤ (12898873978287/25000000000000 : ℝ)^27 := by
    have hnat : (6002062653 : ℕ)^35*25000000000000^27 ≤ 12898873978287^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6002062653 10000000000 12898873978287 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3848779/19531250 : ℝ), (1142242877/2500000000 : ℝ), (6002062653/10000000000 : ℝ)] ![(12178209323053/100000000000000 : ℝ), (36226294754467/100000000000000 : ℝ), (12898873978287/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3848779/19531250 : ℝ)|^35 ≤ (12178209323053/100000000000000 : ℝ)^27
        have hw : |(-3848779/19531250 : ℝ)|=(3848779/19531250 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1142242877/2500000000 : ℝ)|^35 ≤ (36226294754467/100000000000000 : ℝ)^27
        have hw : |(1142242877/2500000000 : ℝ)|=(1142242877/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6002062653/10000000000 : ℝ)|^35 ≤ (12898873978287/25000000000000 : ℝ)^27
        have hw : |(6002062653/10000000000 : ℝ)|=(6002062653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309061_s3_s3_2 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (603204187/1250000000 : ℝ)*x 0 + (1286019637/2000000000 : ℝ)*x 1 + (-945287617/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (603204187/1250000000 : ℝ)^35 ≤ (4860743104313/12500000000000 : ℝ)^27 := by
    have hnat : (603204187 : ℕ)^35*12500000000000^27 ≤ 4860743104313^27*1250000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      603204187 1250000000 4860743104313 12500000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1286019637/2000000000 : ℝ)^35 ≤ (14103704486547/25000000000000 : ℝ)^27 := by
    have hnat : (1286019637 : ℕ)^35*25000000000000^27 ≤ 14103704486547^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1286019637 2000000000 14103704486547 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (945287617/10000000000 : ℝ)^35 ≤ (4699237197979/100000000000000 : ℝ)^27 := by
    have hnat : (945287617 : ℕ)^35*100000000000000^27 ≤ 4699237197979^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      945287617 10000000000 4699237197979 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(603204187/1250000000 : ℝ), (1286019637/2000000000 : ℝ), (-945287617/10000000000 : ℝ)] ![(4860743104313/12500000000000 : ℝ), (14103704486547/25000000000000 : ℝ), (4699237197979/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(603204187/1250000000 : ℝ)|^35 ≤ (4860743104313/12500000000000 : ℝ)^27
        have hw : |(603204187/1250000000 : ℝ)|=(603204187/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1286019637/2000000000 : ℝ)|^35 ≤ (14103704486547/25000000000000 : ℝ)^27
        have hw : |(1286019637/2000000000 : ℝ)|=(1286019637/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-945287617/10000000000 : ℝ)|^35 ≤ (4699237197979/100000000000000 : ℝ)^27
        have hw : |(-945287617/10000000000 : ℝ)|=(945287617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309061_s3_s3_6 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (6238194327/10000000000 : ℝ)*x 0 + (363636607/1250000000 : ℝ)*x 1 + (1746674853/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6238194327/10000000000 : ℝ)^35 ≤ (54241989505359/100000000000000 : ℝ)^27 := by
    have hnat : (6238194327 : ℕ)^35*100000000000000^27 ≤ 54241989505359^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6238194327 10000000000 54241989505359 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (363636607/1250000000 : ℝ)^35 ≤ (5044416651919/25000000000000 : ℝ)^27 := by
    have hnat : (363636607 : ℕ)^35*25000000000000^27 ≤ 5044416651919^27*1250000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      363636607 1250000000 5044416651919 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1746674853/5000000000 : ℝ)^35 ≤ (25580343880337/100000000000000 : ℝ)^27 := by
    have hnat : (1746674853 : ℕ)^35*100000000000000^27 ≤ 25580343880337^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1746674853 5000000000 25580343880337 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6238194327/10000000000 : ℝ), (363636607/1250000000 : ℝ), (1746674853/5000000000 : ℝ)] ![(54241989505359/100000000000000 : ℝ), (5044416651919/25000000000000 : ℝ), (25580343880337/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6238194327/10000000000 : ℝ)|^35 ≤ (54241989505359/100000000000000 : ℝ)^27
        have hw : |(6238194327/10000000000 : ℝ)|=(6238194327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(363636607/1250000000 : ℝ)|^35 ≤ (5044416651919/25000000000000 : ℝ)^27
        have hw : |(363636607/1250000000 : ℝ)|=(363636607/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1746674853/5000000000 : ℝ)|^35 ≤ (25580343880337/100000000000000 : ℝ)^27
        have hw : |(1746674853/5000000000 : ℝ)|=(1746674853/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309061_s3_s3_7 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-1843585611/10000000000 : ℝ)*x 0 + (467586729/1250000000 : ℝ)*x 1 + (852373947/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1843585611/10000000000 : ℝ)^35 ≤ (11170743205589/100000000000000 : ℝ)^27 := by
    have hnat : (1843585611 : ℕ)^35*100000000000000^27 ≤ 11170743205589^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1843585611 10000000000 11170743205589 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (467586729/1250000000 : ℝ)^35 ≤ (27952423738179/100000000000000 : ℝ)^27 := by
    have hnat : (467586729 : ℕ)^35*100000000000000^27 ≤ 27952423738179^27*1250000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      467586729 1250000000 27952423738179 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (852373947/1250000000 : ℝ)^35 ≤ (1521920826309/2500000000000 : ℝ)^27 := by
    have hnat : (852373947 : ℕ)^35*2500000000000^27 ≤ 1521920826309^27*1250000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      852373947 1250000000 1521920826309 2500000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1843585611/10000000000 : ℝ), (467586729/1250000000 : ℝ), (852373947/1250000000 : ℝ)] ![(11170743205589/100000000000000 : ℝ), (27952423738179/100000000000000 : ℝ), (1521920826309/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1843585611/10000000000 : ℝ)|^35 ≤ (11170743205589/100000000000000 : ℝ)^27
        have hw : |(-1843585611/10000000000 : ℝ)|=(1843585611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(467586729/1250000000 : ℝ)|^35 ≤ (27952423738179/100000000000000 : ℝ)^27
        have hw : |(467586729/1250000000 : ℝ)|=(467586729/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(852373947/1250000000 : ℝ)|^35 ≤ (1521920826309/2500000000000 : ℝ)^27
        have hw : |(852373947/1250000000 : ℝ)|=(852373947/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309061_s3_s3_8 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2078456639/5000000000 : ℝ)*x 0 + (-27082227/200000000 : ℝ)*x 1 + (6783204723/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2078456639/5000000000 : ℝ)^35 ≤ (32048980065421/100000000000000 : ℝ)^27 := by
    have hnat : (2078456639 : ℕ)^35*100000000000000^27 ≤ 32048980065421^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2078456639 5000000000 32048980065421 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (27082227/200000000 : ℝ)^35 ≤ (3744008198183/50000000000000 : ℝ)^27 := by
    have hnat : (27082227 : ℕ)^35*50000000000000^27 ≤ 3744008198183^27*200000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      27082227 200000000 3744008198183 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6783204723/10000000000 : ℝ)^35 ≤ (60463003524587/100000000000000 : ℝ)^27 := by
    have hnat : (6783204723 : ℕ)^35*100000000000000^27 ≤ 60463003524587^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6783204723 10000000000 60463003524587 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2078456639/5000000000 : ℝ), (-27082227/200000000 : ℝ), (6783204723/10000000000 : ℝ)] ![(32048980065421/100000000000000 : ℝ), (3744008198183/50000000000000 : ℝ), (60463003524587/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2078456639/5000000000 : ℝ)|^35 ≤ (32048980065421/100000000000000 : ℝ)^27
        have hw : |(2078456639/5000000000 : ℝ)|=(2078456639/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-27082227/200000000 : ℝ)|^35 ≤ (3744008198183/50000000000000 : ℝ)^27
        have hw : |(-27082227/200000000 : ℝ)|=(27082227/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6783204723/10000000000 : ℝ)|^35 ≤ (60463003524587/100000000000000 : ℝ)^27
        have hw : |(6783204723/10000000000 : ℝ)|=(6783204723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309061_s3_s3_9 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2127414889/5000000000 : ℝ)*x 0 + (3660315177/5000000000 : ℝ)*x 1 + (-9054721/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2127414889/5000000000 : ℝ)^35 ≤ (1651548613837/5000000000000 : ℝ)^27 := by
    have hnat : (2127414889 : ℕ)^35*5000000000000^27 ≤ 1651548613837^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2127414889 5000000000 1651548613837 5000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3660315177/5000000000 : ℝ)^35 ≤ (8343047324317/12500000000000 : ℝ)^27 := by
    have hnat : (3660315177 : ℕ)^35*12500000000000^27 ≤ 8343047324317^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3660315177 5000000000 8343047324317 12500000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (9054721/1000000000 : ℝ)^35 ≤ (112324560691/50000000000000 : ℝ)^27 := by
    have hnat : (9054721 : ℕ)^35*50000000000000^27 ≤ 112324560691^27*1000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9054721 1000000000 112324560691 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2127414889/5000000000 : ℝ), (3660315177/5000000000 : ℝ), (-9054721/1000000000 : ℝ)] ![(1651548613837/5000000000000 : ℝ), (8343047324317/12500000000000 : ℝ), (112324560691/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2127414889/5000000000 : ℝ)|^35 ≤ (1651548613837/5000000000000 : ℝ)^27
        have hw : |(2127414889/5000000000 : ℝ)|=(2127414889/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3660315177/5000000000 : ℝ)|^35 ≤ (8343047324317/12500000000000 : ℝ)^27
        have hw : |(3660315177/5000000000 : ℝ)|=(3660315177/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-9054721/1000000000 : ℝ)|^35 ≤ (112324560691/50000000000000 : ℝ)^27
        have hw : |(-9054721/1000000000 : ℝ)|=(9054721/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309061_s3_s3_13 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2943730381/5000000000 : ℝ)*x 0 + (4722418377/10000000000 : ℝ)*x 1 + (1931576977/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2943730381/5000000000 : ℝ)^35 ≤ (50322076295449/100000000000000 : ℝ)^27 := by
    have hnat : (2943730381 : ℕ)^35*100000000000000^27 ≤ 50322076295449^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2943730381 5000000000 50322076295449 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4722418377/10000000000 : ℝ)^35 ≤ (945280295999/2500000000000 : ℝ)^27 := by
    have hnat : (4722418377 : ℕ)^35*2500000000000^27 ≤ 945280295999^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4722418377 10000000000 945280295999 2500000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1931576977/10000000000 : ℝ)^35 ≤ (2966677961137/25000000000000 : ℝ)^27 := by
    have hnat : (1931576977 : ℕ)^35*25000000000000^27 ≤ 2966677961137^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1931576977 10000000000 2966677961137 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2943730381/5000000000 : ℝ), (4722418377/10000000000 : ℝ), (1931576977/10000000000 : ℝ)] ![(50322076295449/100000000000000 : ℝ), (945280295999/2500000000000 : ℝ), (2966677961137/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2943730381/5000000000 : ℝ)|^35 ≤ (50322076295449/100000000000000 : ℝ)^27
        have hw : |(2943730381/5000000000 : ℝ)|=(2943730381/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4722418377/10000000000 : ℝ)|^35 ≤ (945280295999/2500000000000 : ℝ)^27
        have hw : |(4722418377/10000000000 : ℝ)|=(4722418377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1931576977/10000000000 : ℝ)|^35 ≤ (2966677961137/25000000000000 : ℝ)^27
        have hw : |(1931576977/10000000000 : ℝ)|=(1931576977/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309061_s3_s3_14 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-196416913/2500000000 : ℝ)*x 0 + (1125942913/2500000000 : ℝ)*x 1 + (850949203/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (196416913/2500000000 : ℝ)^35 ≤ (369744942339/10000000000000 : ℝ)^27 := by
    have hnat : (196416913 : ℕ)^35*10000000000000^27 ≤ 369744942339^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      196416913 2500000000 369744942339 10000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1125942913/2500000000 : ℝ)^35 ≤ (35557590366251/100000000000000 : ℝ)^27 := by
    have hnat : (1125942913 : ℕ)^35*100000000000000^27 ≤ 35557590366251^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1125942913 2500000000 35557590366251 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (850949203/1250000000 : ℝ)^35 ≤ (12148992039899/20000000000000 : ℝ)^27 := by
    have hnat : (850949203 : ℕ)^35*20000000000000^27 ≤ 12148992039899^27*1250000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      850949203 1250000000 12148992039899 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-196416913/2500000000 : ℝ), (1125942913/2500000000 : ℝ), (850949203/1250000000 : ℝ)] ![(369744942339/10000000000000 : ℝ), (35557590366251/100000000000000 : ℝ), (12148992039899/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-196416913/2500000000 : ℝ)|^35 ≤ (369744942339/10000000000000 : ℝ)^27
        have hw : |(-196416913/2500000000 : ℝ)|=(196416913/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1125942913/2500000000 : ℝ)|^35 ≤ (35557590366251/100000000000000 : ℝ)^27
        have hw : |(1125942913/2500000000 : ℝ)|=(1125942913/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(850949203/1250000000 : ℝ)|^35 ≤ (12148992039899/20000000000000 : ℝ)^27
        have hw : |(850949203/1250000000 : ℝ)|=(850949203/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309061_s3_s3_15 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2077528851/5000000000 : ℝ)*x 0 + (-1375018967/10000000000 : ℝ)*x 1 + (1692951631/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2077528851/5000000000 : ℝ)^35 ≤ (16015218157973/50000000000000 : ℝ)^27 := by
    have hnat : (2077528851 : ℕ)^35*50000000000000^27 ≤ 16015218157973^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2077528851 5000000000 16015218157973 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1375018967/10000000000 : ℝ)^35 ≤ (7638230232983/100000000000000 : ℝ)^27 := by
    have hnat : (1375018967 : ℕ)^35*100000000000000^27 ≤ 7638230232983^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1375018967 10000000000 7638230232983 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1692951631/2500000000 : ℝ)^35 ≤ (60331333433017/100000000000000 : ℝ)^27 := by
    have hnat : (1692951631 : ℕ)^35*100000000000000^27 ≤ 60331333433017^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1692951631 2500000000 60331333433017 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2077528851/5000000000 : ℝ), (-1375018967/10000000000 : ℝ), (1692951631/2500000000 : ℝ)] ![(16015218157973/50000000000000 : ℝ), (7638230232983/100000000000000 : ℝ), (60331333433017/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2077528851/5000000000 : ℝ)|^35 ≤ (16015218157973/50000000000000 : ℝ)^27
        have hw : |(2077528851/5000000000 : ℝ)|=(2077528851/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1375018967/10000000000 : ℝ)|^35 ≤ (7638230232983/100000000000000 : ℝ)^27
        have hw : |(-1375018967/10000000000 : ℝ)|=(1375018967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1692951631/2500000000 : ℝ)|^35 ≤ (60331333433017/100000000000000 : ℝ)^27
        have hw : |(1692951631/2500000000 : ℝ)|=(1692951631/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309061_s3_s3_16 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (612619361/1000000000 : ℝ)*x 0 + (1112567857/2000000000 : ℝ)*x 1 + (-4077813/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (612619361/1000000000 : ℝ)^35 ≤ (52982947618901/100000000000000 : ℝ)^27 := by
    have hnat : (612619361 : ℕ)^35*100000000000000^27 ≤ 52982947618901^27*1000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      612619361 1000000000 52982947618901 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1112567857/2000000000 : ℝ)^35 ≤ (1461096279319/3125000000000 : ℝ)^27 := by
    have hnat : (1112567857 : ℕ)^35*3125000000000^27 ≤ 1461096279319^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1112567857 2000000000 1461096279319 3125000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4077813/400000000 : ℝ)^35 ≤ (261971427441/100000000000000 : ℝ)^27 := by
    have hnat : (4077813 : ℕ)^35*100000000000000^27 ≤ 261971427441^27*400000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4077813 400000000 261971427441 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(612619361/1000000000 : ℝ), (1112567857/2000000000 : ℝ), (-4077813/400000000 : ℝ)] ![(52982947618901/100000000000000 : ℝ), (1461096279319/3125000000000 : ℝ), (261971427441/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(612619361/1000000000 : ℝ)|^35 ≤ (52982947618901/100000000000000 : ℝ)^27
        have hw : |(612619361/1000000000 : ℝ)|=(612619361/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1112567857/2000000000 : ℝ)|^35 ≤ (1461096279319/3125000000000 : ℝ)^27
        have hw : |(1112567857/2000000000 : ℝ)|=(1112567857/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4077813/400000000 : ℝ)|^35 ≤ (261971427441/100000000000000 : ℝ)^27
        have hw : |(-4077813/400000000 : ℝ)|=(4077813/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309061_s3_s3_20 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (7668846191/10000000000 : ℝ)*x 0 + (638546643/2500000000 : ℝ)*x 1 + (1956481/10000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7668846191/10000000000 : ℝ)^35 ≤ (4430533033151/6250000000000 : ℝ)^27 := by
    have hnat : (7668846191 : ℕ)^35*6250000000000^27 ≤ 4430533033151^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7668846191 10000000000 4430533033151 6250000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (638546643/2500000000 : ℝ)^35 ≤ (17046050206657/100000000000000 : ℝ)^27 := by
    have hnat : (638546643 : ℕ)^35*100000000000000^27 ≤ 17046050206657^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      638546643 2500000000 17046050206657 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1956481/10000000 : ℝ)^35 ≤ (12065421250521/100000000000000 : ℝ)^27 := by
    have hnat : (1956481 : ℕ)^35*100000000000000^27 ≤ 12065421250521^27*10000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1956481 10000000 12065421250521 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7668846191/10000000000 : ℝ), (638546643/2500000000 : ℝ), (1956481/10000000 : ℝ)] ![(4430533033151/6250000000000 : ℝ), (17046050206657/100000000000000 : ℝ), (12065421250521/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7668846191/10000000000 : ℝ)|^35 ≤ (4430533033151/6250000000000 : ℝ)^27
        have hw : |(7668846191/10000000000 : ℝ)|=(7668846191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(638546643/2500000000 : ℝ)|^35 ≤ (17046050206657/100000000000000 : ℝ)^27
        have hw : |(638546643/2500000000 : ℝ)|=(638546643/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1956481/10000000 : ℝ)|^35 ≤ (12065421250521/100000000000000 : ℝ)^27
        have hw : |(1956481/10000000 : ℝ)|=(1956481/10000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309061_s3_s3_21 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-174383657/2500000000 : ℝ)*x 0 + (225671547/400000000 : ℝ)*x 1 + (5787196129/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (174383657/2500000000 : ℝ)^35 ≤ (792243349979/25000000000000 : ℝ)^27 := by
    have hnat : (174383657 : ℕ)^35*25000000000000^27 ≤ 792243349979^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      174383657 2500000000 792243349979 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (225671547/400000000 : ℝ)^35 ≤ (47617055631633/100000000000000 : ℝ)^27 := by
    have hnat : (225671547 : ℕ)^35*100000000000000^27 ≤ 47617055631633^27*400000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      225671547 400000000 47617055631633 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5787196129/10000000000 : ℝ)^35 ≤ (24606985477217/50000000000000 : ℝ)^27 := by
    have hnat : (5787196129 : ℕ)^35*50000000000000^27 ≤ 24606985477217^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5787196129 10000000000 24606985477217 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-174383657/2500000000 : ℝ), (225671547/400000000 : ℝ), (5787196129/10000000000 : ℝ)] ![(792243349979/25000000000000 : ℝ), (47617055631633/100000000000000 : ℝ), (24606985477217/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-174383657/2500000000 : ℝ)|^35 ≤ (792243349979/25000000000000 : ℝ)^27
        have hw : |(-174383657/2500000000 : ℝ)|=(174383657/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(225671547/400000000 : ℝ)|^35 ≤ (47617055631633/100000000000000 : ℝ)^27
        have hw : |(225671547/400000000 : ℝ)|=(225671547/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5787196129/10000000000 : ℝ)|^35 ≤ (24606985477217/50000000000000 : ℝ)^27
        have hw : |(5787196129/10000000000 : ℝ)|=(5787196129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309061_s3_s3_22 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1529102593/2500000000 : ℝ)*x 0 + (-186516709/2500000000 : ℝ)*x 1 + (527739381/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1529102593/2500000000 : ℝ)^35 ≤ (52873292351439/100000000000000 : ℝ)^27 := by
    have hnat : (1529102593 : ℕ)^35*100000000000000^27 ≤ 52873292351439^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1529102593 2500000000 52873292351439 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (186516709/2500000000 : ℝ)^35 ≤ (3457689197453/100000000000000 : ℝ)^27 := by
    have hnat : (186516709 : ℕ)^35*100000000000000^27 ≤ 3457689197453^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      186516709 2500000000 3457689197453 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (527739381/1000000000 : ℝ)^35 ≤ (43669018436961/100000000000000 : ℝ)^27 := by
    have hnat : (527739381 : ℕ)^35*100000000000000^27 ≤ 43669018436961^27*1000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      527739381 1000000000 43669018436961 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1529102593/2500000000 : ℝ), (-186516709/2500000000 : ℝ), (527739381/1000000000 : ℝ)] ![(52873292351439/100000000000000 : ℝ), (3457689197453/100000000000000 : ℝ), (43669018436961/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1529102593/2500000000 : ℝ)|^35 ≤ (52873292351439/100000000000000 : ℝ)^27
        have hw : |(1529102593/2500000000 : ℝ)|=(1529102593/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-186516709/2500000000 : ℝ)|^35 ≤ (3457689197453/100000000000000 : ℝ)^27
        have hw : |(-186516709/2500000000 : ℝ)|=(186516709/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(527739381/1000000000 : ℝ)|^35 ≤ (43669018436961/100000000000000 : ℝ)^27
        have hw : |(527739381/1000000000 : ℝ)|=(527739381/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309061_s3_s3_23 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2020020363/5000000000 : ℝ)*x 0 + (914733491/1250000000 : ℝ)*x 1 + (-563363389/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2020020363/5000000000 : ℝ)^35 ≤ (617716628283/2000000000000 : ℝ)^27 := by
    have hnat : (2020020363 : ℕ)^35*2000000000000^27 ≤ 617716628283^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2020020363 5000000000 617716628283 2000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (914733491/1250000000 : ℝ)^35 ≤ (13342346415303/20000000000000 : ℝ)^27 := by
    have hnat : (914733491 : ℕ)^35*20000000000000^27 ≤ 13342346415303^27*1250000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      914733491 1250000000 13342346415303 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (563363389/10000000000 : ℝ)^35 ≤ (2402436487641/100000000000000 : ℝ)^27 := by
    have hnat : (563363389 : ℕ)^35*100000000000000^27 ≤ 2402436487641^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      563363389 10000000000 2402436487641 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2020020363/5000000000 : ℝ), (914733491/1250000000 : ℝ), (-563363389/10000000000 : ℝ)] ![(617716628283/2000000000000 : ℝ), (13342346415303/20000000000000 : ℝ), (2402436487641/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2020020363/5000000000 : ℝ)|^35 ≤ (617716628283/2000000000000 : ℝ)^27
        have hw : |(2020020363/5000000000 : ℝ)|=(2020020363/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(914733491/1250000000 : ℝ)|^35 ≤ (13342346415303/20000000000000 : ℝ)^27
        have hw : |(914733491/1250000000 : ℝ)|=(914733491/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-563363389/10000000000 : ℝ)|^35 ≤ (2402436487641/100000000000000 : ℝ)^27
        have hw : |(-563363389/10000000000 : ℝ)|=(563363389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309061_s3_s3_27 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2033523079/2500000000 : ℝ)*x 0 + (2973779/15625000 : ℝ)*x 1 + (15069977/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2033523079/2500000000 : ℝ)^35 ≤ (76512785785321/100000000000000 : ℝ)^27 := by
    have hnat : (2033523079 : ℕ)^35*100000000000000^27 ≤ 76512785785321^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2033523079 2500000000 76512785785321 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2973779/15625000 : ℝ)^35 ≤ (2910340699371/25000000000000 : ℝ)^27 := by
    have hnat : (2973779 : ℕ)^35*25000000000000^27 ≤ 2910340699371^27*15625000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2973779 15625000 2910340699371 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (15069977/78125000 : ℝ)^35 ≤ (11845851400557/100000000000000 : ℝ)^27 := by
    have hnat : (15069977 : ℕ)^35*100000000000000^27 ≤ 11845851400557^27*78125000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      15069977 78125000 11845851400557 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2033523079/2500000000 : ℝ), (2973779/15625000 : ℝ), (15069977/78125000 : ℝ)] ![(76512785785321/100000000000000 : ℝ), (2910340699371/25000000000000 : ℝ), (11845851400557/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2033523079/2500000000 : ℝ)|^35 ≤ (76512785785321/100000000000000 : ℝ)^27
        have hw : |(2033523079/2500000000 : ℝ)|=(2033523079/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2973779/15625000 : ℝ)|^35 ≤ (2910340699371/25000000000000 : ℝ)^27
        have hw : |(2973779/15625000 : ℝ)|=(2973779/15625000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(15069977/78125000 : ℝ)|^35 ≤ (11845851400557/100000000000000 : ℝ)^27
        have hw : |(15069977/78125000 : ℝ)|=(15069977/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c309061_s3 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (159247/100000 : ℝ) (91323/50000 : ℝ) (77509/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]])
    (hprev2 : (0 : ℝ) ≤ ((673/1000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(673/1000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(34853/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(34853/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(64621/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(64621/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((23017/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(23017/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(52481/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(52481/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(4751/10000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(4751/10000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (77509/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (77509/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (77509/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (77509/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (77509/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (77509/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base11 : ((1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).2]
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base53 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2,f.sum]
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
  rcases hprev2 with ⟨ratio_s2_0,ratio_s2_1,ratio_s2_2⟩
  have s3_pow0 : (673/1000 : ℝ) ^ (69/16 : ℝ) ≤ (18126542117576953307/100000000000000000000 : ℝ) := by
    have hpowers : (673/1000 : ℝ)^69 ≤ (18126542117576953307/100000000000000000000 : ℝ)^16 := by
      have hnat : (673 : ℕ)^69*100000000000000000000^16 ≤ 18126542117576953307^16*1000^69 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        673 1000 18126542117576953307 100000000000000000000 69 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (673/1000 : ℝ)) (X := (18126542117576953307/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s3_corner0a : (118126542117576953307/100000000000000000000 : ℝ) ≤ (10393844851487377/10000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (118126542117576953307/100000000000000000000 : ℝ)^16 ≤ (10393844851487377/10000000000000000 : ℝ)^69 := by
      have hnat : (118126542117576953307 : ℕ)^16*10000000000000000^69 ≤ 10393844851487377^69*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        118126542117576953307 100000000000000000000 10393844851487377 10000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10393844851487377/10000000000000000 : ℝ)) (X := (118126542117576953307/100000000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s3_corner0b : (68126542117576953307/50000000000000000000 : ℝ) ≤ (10743672838120259/10000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (68126542117576953307/50000000000000000000 : ℝ)^16 ≤ (10743672838120259/10000000000000000 : ℝ)^69 := by
      have hnat : (68126542117576953307 : ℕ)^16*10000000000000000^69 ≤ 10743672838120259^69*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        68126542117576953307 50000000000000000000 10743672838120259 10000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10743672838120259/10000000000000000 : ℝ)) (X := (68126542117576953307/50000000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have major_s3_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(393844851487377/6730000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(174913993316441/3365000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (69/16 : ℝ)) (rho := (673/1000 : ℝ)) (alpha := (393844851487377/6730000000000000 : ℝ)) (beta := (174913993316441/3365000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow0,s3_corner0a]) (by linarith only [s3_pow0,s3_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (673/1000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(393844851487377/6730000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(174913993316441/3365000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s3_pow1 : (34853/50000 : ℝ) ^ (69/16 : ℝ) ≤ (10545631165330481461/50000000000000000000 : ℝ) := by
    have hpowers : (34853/50000 : ℝ)^69 ≤ (10545631165330481461/50000000000000000000 : ℝ)^16 := by
      have hnat : (34853 : ℕ)^69*50000000000000000000^16 ≤ 10545631165330481461^16*50000^69 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        34853 50000 10545631165330481461 50000000000000000000 69 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (34853/50000 : ℝ)) (X := (10545631165330481461/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s3_corner1a : (60545631165330481461/50000000000000000000 : ℝ) ≤ (65336001447463/62500000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (60545631165330481461/50000000000000000000 : ℝ)^16 ≤ (65336001447463/62500000000000 : ℝ)^69 := by
      have hnat : (60545631165330481461 : ℕ)^16*62500000000000^69 ≤ 65336001447463^69*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        60545631165330481461 50000000000000000000 65336001447463 62500000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (65336001447463/62500000000000 : ℝ)) (X := (60545631165330481461/50000000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s3_corner1b : (35545631165330481461/25000000000000000000 : ℝ) ≤ (2170064276853743/2000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (35545631165330481461/25000000000000000000 : ℝ)^16 ≤ (2170064276853743/2000000000000000 : ℝ)^69 := by
      have hnat : (35545631165330481461 : ℕ)^16*2000000000000000^69 ≤ 2170064276853743^69*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        35545631165330481461 25000000000000000000 2170064276853743 2000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2170064276853743/2000000000000000 : ℝ)) (X := (35545631165330481461/25000000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have major_s3_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(2836001447463/43566250000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(6100940810379/107240000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (69/16 : ℝ)) (rho := (34853/50000 : ℝ)) (alpha := (2836001447463/43566250000000 : ℝ)) (beta := (6100940810379/107240000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow1,s3_corner1a]) (by linarith only [s3_pow1,s3_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (34853/50000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(2836001447463/43566250000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(6100940810379/107240000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s3_pow2 : (64621/100000 : ℝ) ^ (69/16 : ℝ) ≤ (3803439210426259417/25000000000000000000 : ℝ) := by
    have hpowers : (64621/100000 : ℝ)^69 ≤ (3803439210426259417/25000000000000000000 : ℝ)^16 := by
      have hnat : (64621 : ℕ)^69*25000000000000000000^16 ≤ 3803439210426259417^16*100000^69 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        64621 100000 3803439210426259417 25000000000000000000 69 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (64621/100000 : ℝ)) (X := (3803439210426259417/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s3_corner2a : (28803439210426259417/25000000000000000000 : ℝ) ≤ (10333843390265673/10000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (28803439210426259417/25000000000000000000 : ℝ)^16 ≤ (10333843390265673/10000000000000000 : ℝ)^69 := by
      have hnat : (28803439210426259417 : ℕ)^16*10000000000000000^69 ≤ 10333843390265673^69*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        28803439210426259417 25000000000000000000 10333843390265673 10000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10333843390265673/10000000000000000 : ℝ)) (X := (28803439210426259417/25000000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s3_corner2b : (16303439210426259417/12500000000000000000 : ℝ) ≤ (10635362125084367/10000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (16303439210426259417/12500000000000000000 : ℝ)^16 ≤ (10635362125084367/10000000000000000 : ℝ)^69 := by
      have hnat : (16303439210426259417 : ℕ)^16*10000000000000000^69 ≤ 10635362125084367^69*12500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16303439210426259417 12500000000000000000 10635362125084367 10000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10635362125084367/10000000000000000 : ℝ)) (X := (16303439210426259417/12500000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have major_s3_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(333843390265673/6462100000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(150759367409347/3231050000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (69/16 : ℝ)) (rho := (64621/100000 : ℝ)) (alpha := (333843390265673/6462100000000000 : ℝ)) (beta := (150759367409347/3231050000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow2,s3_corner2a]) (by linarith only [s3_pow2,s3_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (64621/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(333843390265673/6462100000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(150759367409347/3231050000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s3_0 : ((-3848779/19531250 : ℝ)*X 0 0+(1142242877/2500000000 : ℝ)*X 0 1+(6002062653/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c309061_s3_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_2 : ((603204187/1250000000 : ℝ)*X 2 0+(1286019637/2000000000 : ℝ)*X 2 1+(-945287617/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c309061_s3_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_6 : ((6238194327/10000000000 : ℝ)*X 0 0+(363636607/1250000000 : ℝ)*X 0 1+(1746674853/5000000000 : ℝ)*X 0 2+(6238194327/10000000000 : ℝ)*X 1 0+(363636607/1250000000 : ℝ)*X 1 1+(1746674853/5000000000 : ℝ)*X 1 2+(6238194327/10000000000 : ℝ)*X 2 0+(363636607/1250000000 : ℝ)*X 2 1+(1746674853/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c309061_s3_s3_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_7 : ((-1843585611/10000000000 : ℝ)*X 0 0+(467586729/1250000000 : ℝ)*X 0 1+(852373947/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c309061_s3_s3_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_8 : ((2078456639/5000000000 : ℝ)*X 1 0+(-27082227/200000000 : ℝ)*X 1 1+(6783204723/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c309061_s3_s3_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_9 : ((2127414889/5000000000 : ℝ)*X 2 0+(3660315177/5000000000 : ℝ)*X 2 1+(-9054721/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c309061_s3_s3_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_13 : ((2943730381/5000000000 : ℝ)*X 0 0+(4722418377/10000000000 : ℝ)*X 0 1+(1931576977/10000000000 : ℝ)*X 0 2+(2943730381/5000000000 : ℝ)*X 1 0+(4722418377/10000000000 : ℝ)*X 1 1+(1931576977/10000000000 : ℝ)*X 1 2+(2943730381/5000000000 : ℝ)*X 2 0+(4722418377/10000000000 : ℝ)*X 2 1+(1931576977/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c309061_s3_s3_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_14 : ((-196416913/2500000000 : ℝ)*X 0 0+(1125942913/2500000000 : ℝ)*X 0 1+(850949203/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c309061_s3_s3_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_15 : ((2077528851/5000000000 : ℝ)*X 1 0+(-1375018967/10000000000 : ℝ)*X 1 1+(1692951631/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c309061_s3_s3_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_16 : ((612619361/1000000000 : ℝ)*X 2 0+(1112567857/2000000000 : ℝ)*X 2 1+(-4077813/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c309061_s3_s3_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_20 : ((7668846191/10000000000 : ℝ)*X 0 0+(638546643/2500000000 : ℝ)*X 0 1+(1956481/10000000 : ℝ)*X 0 2+(7668846191/10000000000 : ℝ)*X 1 0+(638546643/2500000000 : ℝ)*X 1 1+(1956481/10000000 : ℝ)*X 1 2+(7668846191/10000000000 : ℝ)*X 2 0+(638546643/2500000000 : ℝ)*X 2 1+(1956481/10000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c309061_s3_s3_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_21 : ((-174383657/2500000000 : ℝ)*X 0 0+(225671547/400000000 : ℝ)*X 0 1+(5787196129/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c309061_s3_s3_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_22 : ((1529102593/2500000000 : ℝ)*X 1 0+(-186516709/2500000000 : ℝ)*X 1 1+(527739381/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c309061_s3_s3_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_23 : ((2020020363/5000000000 : ℝ)*X 2 0+(914733491/1250000000 : ℝ)*X 2 1+(-563363389/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c309061_s3_s3_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_27 : ((2033523079/2500000000 : ℝ)*X 0 0+(2973779/15625000 : ℝ)*X 0 1+(15069977/78125000 : ℝ)*X 0 2+(2033523079/2500000000 : ℝ)*X 1 0+(2973779/15625000 : ℝ)*X 1 1+(15069977/78125000 : ℝ)*X 1 2+(2033523079/2500000000 : ℝ)*X 2 0+(2973779/15625000 : ℝ)*X 2 1+(15069977/78125000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c309061_s3_s3_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s3_0 : (0 : ℝ) ≤ ((23017/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(23017/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1017400011654330471721865711007/270670470508750000000000000000000000 : ℝ) := by norm_num
    linear_combination (13599/50000000000 : ℝ)*(base19) + (59210267957/100000000000 : ℝ)*(base59) + (527037/1000000000000 : ℝ)*(base60) + (257786883277/62500000000 : ℝ)*(major_s3_0) + (257786883277/62500000000 : ℝ)*(major_s3_1) + (257786883277/62500000000 : ℝ)*(major_s3_2) + (3233973/200000000000 : ℝ)*(sp_s3_0) + (14339043/1000000000000 : ℝ)*(sp_s3_6) + (5659104547437/1000000000000 : ℝ)*(sp_s3_7) + (1414440363093/250000000000 : ℝ)*(sp_s3_8) + (2829536417361/500000000000 : ℝ)*(sp_s3_9) + (323755494447/125000000000 : ℝ)*(sp_s3_13) + (27179859/20000000000 : ℝ)*(sp_s3_15) + (2394129/50000000000 : ℝ)*(sp_s3_23) + (2590058294619/1000000000000 : ℝ)*(f.failure) + (5659120717301/1000000000000 : ℝ)*(f.sum) + (3323017158724310189/8043698975000000000000000000000 : ℝ)*base62 + (459483852192531/807762500000000000000000000 : ℝ)*base64 + (115215631637/766000000000000000000000 : ℝ)*base66 + (1020378344543977/3231050000000000000000000000 : ℝ)*base68 + (7786849958397330183/13590604062500000000000000000000 : ℝ)*base70 + (130160597249311/420625000000000000000000000 : ℝ)*base72 + (1606570972547/49790000000000000000000000 : ℝ)*base74 + (65116649375821/420625000000000000000000000 : ℝ)*base76 + (953034147308387/161099375000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base81 + (1/1000000000000 : ℝ)*base83 + (1/1000000000000 : ℝ)*base85 + (8107/100000000000000000 : ℝ)*base86 + (8107/100000000000000000 : ℝ)*base88 + (8107/100000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s3_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(52481/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(52481/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (222104325045859924508150727/56305892825000000000000000000000 : ℝ) := by norm_num
    linear_combination (363901/1000000000000 : ℝ)*(base19) + (11413/100000000000 : ℝ)*(base39) + (300369/125000000000 : ℝ)*(base53) + (39033790229/250000000000 : ℝ)*(base59) + (3890833994919/1000000000000 : ℝ)*(major_s3_0) + (3890833994919/1000000000000 : ℝ)*(major_s3_1) + (3890831591967/1000000000000 : ℝ)*(major_s3_2) + (382747/250000000000 : ℝ)*(sp_s3_6) + (721049/62500000000 : ℝ)*(sp_s3_7) + (166824464047/31250000000 : ℝ)*(sp_s3_14) + (5338394022387/1000000000000 : ℝ)*(sp_s3_15) + (133459919731/25000000000 : ℝ)*(sp_s3_16) + (1221615211957/500000000000 : ℝ)*(sp_s3_20) + (37930823/1000000000000 : ℝ)*(sp_s3_27) + (610817471431/250000000000 : ℝ)*(f.failure) + (133459919731/25000000000 : ℝ)*(f.sum) + (79632486355479559497/225223571300000000000000000000000 : ℝ)*base62 + (1738532335104309/3231050000000000000000000000 : ℝ)*base64 + (79213606495603/107240000000000000000000000 : ℝ)*base66 + (6574189573535529/6462100000000000000000000000 : ℝ)*base68 + (68945909696208130123/434899330000000000000000000000000 : ℝ)*base71 + (1599618307282721/3365000000000000000000000000 : ℝ)*base72 + (181981713812839/174265000000000000000000000 : ℝ)*base74 + (5488873394530537/6730000000000000000000000000 : ℝ)*base76 + (50793828880698039/563847812500000000000000000000 : ℝ)*base79 + (2543/25000000000000000 : ℝ)*base86 + (2543/25000000000000000 : ℝ)*base88 + (2543/25000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s3_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(4751/10000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(4751/10000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (735157836809609907550740094287/145745637966250000000000000000000000 : ℝ) := by norm_num
    linear_combination (5485069/1000000000000 : ℝ)*(base11) + (1831721/500000000000 : ℝ)*(base15) + (43601644697/200000000000 : ℝ)*(base40) + (200279670777/1000000000000 : ℝ)*(base59) + (3352084303737/1000000000000 : ℝ)*(major_s3_0) + (3352084303737/1000000000000 : ℝ)*(major_s3_1) + (3352084303737/1000000000000 : ℝ)*(major_s3_2) + (227147/250000000000 : ℝ)*(sp_s3_0) + (727287/500000000000 : ℝ)*(sp_s3_2) + (26930659/1000000000000 : ℝ)*(sp_s3_9) + (919840275717/200000000000 : ℝ)*(sp_s3_21) + (359312821/78125000 : ℝ)*(sp_s3_22) + (459917938701/100000000000 : ℝ)*(sp_s3_23) + (2104959153853/1000000000000 : ℝ)*(sp_s3_27) + (2104959153853/1000000000000 : ℝ)*(f.failure) + (2299603886121/500000000000 : ℝ)*(f.sum) + (5923569893164509401/17324890100000000000000000000000 : ℝ)*base63 + (419297604525533/1615525000000000000000000000 : ℝ)*base65 + (6537173724339/21448000000000000000000000 : ℝ)*base67 + (2887099310010921/6462100000000000000000000000 : ℝ)*base69 + (105395238622611120829/434899330000000000000000000000000 : ℝ)*base71 + (680214605408017/3365000000000000000000000000 : ℝ)*base73 + (59144489781/13405000000000000000000000 : ℝ)*base75 + (4160941758000151/6730000000000000000000000000 : ℝ)*base76 + (190510913690545369/1127695625000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base85 + (71309/100000000000000000 : ℝ)*base86 + (71309/100000000000000000 : ℝ)*base88 + (71309/100000000000000000 : ℝ)*base90 + hcertificate_margin
  exact ⟨ratio_s3_0,ratio_s3_1,ratio_s3_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (159247/100000 : ℝ) (91323/50000 : ℝ) (77509/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]])
    (hprev2 : (0 : ℝ) ≤ ((673/1000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(673/1000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(34853/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(34853/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(64621/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(64621/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((23017/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(23017/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(52481/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(52481/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(4751/10000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(4751/10000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c309061_s3 p hpa hpb X hX hprev2

#print axioms solution
