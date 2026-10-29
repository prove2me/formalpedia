-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c311053_s3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T23:59:11.499151+00:00
-- url     : https://prove2.me/submissions/732849c0-16db-4d3d-899a-244ce9ec9a33

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
theorem collision_support_c311053_s3_s3_0 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (-2507749043/10000000000 : ℝ)*x 0 + (201766033/400000000 : ℝ)*x 1 + (5057682173/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2507749043/10000000000 : ℝ)^9 ≤ (16890828464471/100000000000000 : ℝ)^7 := by
    have hnat : (2507749043 : ℕ)^9*100000000000000^7 ≤ 16890828464471^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2507749043 10000000000 16890828464471 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (201766033/400000000 : ℝ)^9 ≤ (41483020192387/100000000000000 : ℝ)^7 := by
    have hnat : (201766033 : ℕ)^9*100000000000000^7 ≤ 41483020192387^7*400000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      201766033 400000000 41483020192387 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5057682173/10000000000 : ℝ)^9 ≤ (10406537833211/25000000000000 : ℝ)^7 := by
    have hnat : (5057682173 : ℕ)^9*25000000000000^7 ≤ 10406537833211^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5057682173 10000000000 10406537833211 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2507749043/10000000000 : ℝ), (201766033/400000000 : ℝ), (5057682173/10000000000 : ℝ)] ![(16890828464471/100000000000000 : ℝ), (41483020192387/100000000000000 : ℝ), (10406537833211/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2507749043/10000000000 : ℝ)|^9 ≤ (16890828464471/100000000000000 : ℝ)^7
        have hw : |(-2507749043/10000000000 : ℝ)|=(2507749043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(201766033/400000000 : ℝ)|^9 ≤ (41483020192387/100000000000000 : ℝ)^7
        have hw : |(201766033/400000000 : ℝ)|=(201766033/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5057682173/10000000000 : ℝ)|^9 ≤ (10406537833211/25000000000000 : ℝ)^7
        have hw : |(5057682173/10000000000 : ℝ)|=(5057682173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311053_s3_s3_1 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (1123318243/2500000000 : ℝ)*x 0 + (-505554039/2500000000 : ℝ)*x 1 + (5962892607/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1123318243/2500000000 : ℝ)^9 ≤ (35751562971777/100000000000000 : ℝ)^7 := by
    have hnat : (1123318243 : ℕ)^9*100000000000000^7 ≤ 35751562971777^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1123318243 2500000000 35751562971777 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (505554039/2500000000 : ℝ)^9 ≤ (12808332623991/100000000000000 : ℝ)^7 := by
    have hnat : (505554039 : ℕ)^9*100000000000000^7 ≤ 12808332623991^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      505554039 2500000000 12808332623991 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5962892607/10000000000 : ℝ)^9 ≤ (51440104395563/100000000000000 : ℝ)^7 := by
    have hnat : (5962892607 : ℕ)^9*100000000000000^7 ≤ 51440104395563^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5962892607 10000000000 51440104395563 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1123318243/2500000000 : ℝ), (-505554039/2500000000 : ℝ), (5962892607/10000000000 : ℝ)] ![(35751562971777/100000000000000 : ℝ), (12808332623991/100000000000000 : ℝ), (51440104395563/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1123318243/2500000000 : ℝ)|^9 ≤ (35751562971777/100000000000000 : ℝ)^7
        have hw : |(1123318243/2500000000 : ℝ)|=(1123318243/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-505554039/2500000000 : ℝ)|^9 ≤ (12808332623991/100000000000000 : ℝ)^7
        have hw : |(-505554039/2500000000 : ℝ)|=(505554039/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5962892607/10000000000 : ℝ)|^9 ≤ (51440104395563/100000000000000 : ℝ)^7
        have hw : |(5962892607/10000000000 : ℝ)|=(5962892607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311053_s3_s3_2 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (4509883959/10000000000 : ℝ)*x 0 + (297791861/500000000 : ℝ)*x 1 + (-2010936891/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4509883959/10000000000 : ℝ)^9 ≤ (7184316690199/20000000000000 : ℝ)^7 := by
    have hnat : (4509883959 : ℕ)^9*20000000000000^7 ≤ 7184316690199^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4509883959 10000000000 7184316690199 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (297791861/500000000 : ℝ)^9 ≤ (3210116435931/6250000000000 : ℝ)^7 := by
    have hnat : (297791861 : ℕ)^9*6250000000000^7 ≤ 3210116435931^7*500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      297791861 500000000 3210116435931 6250000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2010936891/10000000000 : ℝ)^9 ≤ (12716553556273/100000000000000 : ℝ)^7 := by
    have hnat : (2010936891 : ℕ)^9*100000000000000^7 ≤ 12716553556273^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2010936891 10000000000 12716553556273 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4509883959/10000000000 : ℝ), (297791861/500000000 : ℝ), (-2010936891/10000000000 : ℝ)] ![(7184316690199/20000000000000 : ℝ), (3210116435931/6250000000000 : ℝ), (12716553556273/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4509883959/10000000000 : ℝ)|^9 ≤ (7184316690199/20000000000000 : ℝ)^7
        have hw : |(4509883959/10000000000 : ℝ)|=(4509883959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(297791861/500000000 : ℝ)|^9 ≤ (3210116435931/6250000000000 : ℝ)^7
        have hw : |(297791861/500000000 : ℝ)|=(297791861/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2010936891/10000000000 : ℝ)|^9 ≤ (12716553556273/100000000000000 : ℝ)^7
        have hw : |(-2010936891/10000000000 : ℝ)|=(2010936891/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311053_s3_s3_6 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (3242114267/5000000000 : ℝ)*x 0 + (1510009191/5000000000 : ℝ)*x 1 + (187417943/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3242114267/5000000000 : ℝ)^9 ≤ (5729326143101/10000000000000 : ℝ)^7 := by
    have hnat : (3242114267 : ℕ)^9*10000000000000^7 ≤ 5729326143101^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3242114267 5000000000 5729326143101 10000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1510009191/5000000000 : ℝ)^9 ≤ (21450671734003/100000000000000 : ℝ)^7 := by
    have hnat : (1510009191 : ℕ)^9*100000000000000^7 ≤ 21450671734003^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1510009191 5000000000 21450671734003 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (187417943/625000000 : ℝ)^9 ≤ (2657008352733/12500000000000 : ℝ)^7 := by
    have hnat : (187417943 : ℕ)^9*12500000000000^7 ≤ 2657008352733^7*625000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      187417943 625000000 2657008352733 12500000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3242114267/5000000000 : ℝ), (1510009191/5000000000 : ℝ), (187417943/625000000 : ℝ)] ![(5729326143101/10000000000000 : ℝ), (21450671734003/100000000000000 : ℝ), (2657008352733/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3242114267/5000000000 : ℝ)|^9 ≤ (5729326143101/10000000000000 : ℝ)^7
        have hw : |(3242114267/5000000000 : ℝ)|=(3242114267/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1510009191/5000000000 : ℝ)|^9 ≤ (21450671734003/100000000000000 : ℝ)^7
        have hw : |(1510009191/5000000000 : ℝ)|=(1510009191/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(187417943/625000000 : ℝ)|^9 ≤ (2657008352733/12500000000000 : ℝ)^7
        have hw : |(187417943/625000000 : ℝ)|=(187417943/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311053_s3_s3_7 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (-1236470557/5000000000 : ℝ)*x 0 + (4452157233/10000000000 : ℝ)*x 1 + (1414387889/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1236470557/5000000000 : ℝ)^9 ≤ (207374950401/1250000000000 : ℝ)^7 := by
    have hnat : (1236470557 : ℕ)^9*1250000000000^7 ≤ 207374950401^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1236470557 5000000000 207374950401 1250000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4452157233/10000000000 : ℝ)^9 ≤ (7066299793471/20000000000000 : ℝ)^7 := by
    have hnat : (4452157233 : ℕ)^9*20000000000000^7 ≤ 7066299793471^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4452157233 10000000000 7066299793471 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1414387889/2500000000 : ℝ)^9 ≤ (48078504978867/100000000000000 : ℝ)^7 := by
    have hnat : (1414387889 : ℕ)^9*100000000000000^7 ≤ 48078504978867^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1414387889 2500000000 48078504978867 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1236470557/5000000000 : ℝ), (4452157233/10000000000 : ℝ), (1414387889/2500000000 : ℝ)] ![(207374950401/1250000000000 : ℝ), (7066299793471/20000000000000 : ℝ), (48078504978867/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1236470557/5000000000 : ℝ)|^9 ≤ (207374950401/1250000000000 : ℝ)^7
        have hw : |(-1236470557/5000000000 : ℝ)|=(1236470557/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4452157233/10000000000 : ℝ)|^9 ≤ (7066299793471/20000000000000 : ℝ)^7
        have hw : |(4452157233/10000000000 : ℝ)|=(4452157233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1414387889/2500000000 : ℝ)|^9 ≤ (48078504978867/100000000000000 : ℝ)^7
        have hw : |(1414387889/2500000000 : ℝ)|=(1414387889/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311053_s3_s3_8 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (2171208853/5000000000 : ℝ)*x 0 + (-443466973/2500000000 : ℝ)*x 1 + (6278050117/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2171208853/5000000000 : ℝ)^9 ≤ (17107885820531/50000000000000 : ℝ)^7 := by
    have hnat : (2171208853 : ℕ)^9*50000000000000^7 ≤ 17107885820531^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2171208853 5000000000 17107885820531 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (443466973/2500000000 : ℝ)^9 ≤ (5411246963279/50000000000000 : ℝ)^7 := by
    have hnat : (443466973 : ℕ)^9*50000000000000^7 ≤ 5411246963279^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      443466973 2500000000 5411246963279 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6278050117/10000000000 : ℝ)^9 ≤ (54961734421049/100000000000000 : ℝ)^7 := by
    have hnat : (6278050117 : ℕ)^9*100000000000000^7 ≤ 54961734421049^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6278050117 10000000000 54961734421049 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2171208853/5000000000 : ℝ), (-443466973/2500000000 : ℝ), (6278050117/10000000000 : ℝ)] ![(17107885820531/50000000000000 : ℝ), (5411246963279/50000000000000 : ℝ), (54961734421049/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2171208853/5000000000 : ℝ)|^9 ≤ (17107885820531/50000000000000 : ℝ)^7
        have hw : |(2171208853/5000000000 : ℝ)|=(2171208853/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-443466973/2500000000 : ℝ)|^9 ≤ (5411246963279/50000000000000 : ℝ)^7
        have hw : |(-443466973/2500000000 : ℝ)|=(443466973/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6278050117/10000000000 : ℝ)|^9 ≤ (54961734421049/100000000000000 : ℝ)^7
        have hw : |(6278050117/10000000000 : ℝ)|=(6278050117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311053_s3_s3_9 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (544883321/1250000000 : ℝ)*x 0 + (324821577/500000000 : ℝ)*x 1 + (-356820637/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (544883321/1250000000 : ℝ)^9 ≤ (34384528468747/100000000000000 : ℝ)^7 := by
    have hnat : (544883321 : ℕ)^9*100000000000000^7 ≤ 34384528468747^7*1250000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      544883321 1250000000 34384528468747 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (324821577/500000000 : ℝ)^9 ≤ (2297277138503/4000000000000 : ℝ)^7 := by
    have hnat : (324821577 : ℕ)^9*4000000000000^7 ≤ 2297277138503^7*500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      324821577 500000000 2297277138503 4000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (356820637/2500000000 : ℝ)^9 ≤ (4091771524937/50000000000000 : ℝ)^7 := by
    have hnat : (356820637 : ℕ)^9*50000000000000^7 ≤ 4091771524937^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      356820637 2500000000 4091771524937 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(544883321/1250000000 : ℝ), (324821577/500000000 : ℝ), (-356820637/2500000000 : ℝ)] ![(34384528468747/100000000000000 : ℝ), (2297277138503/4000000000000 : ℝ), (4091771524937/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(544883321/1250000000 : ℝ)|^9 ≤ (34384528468747/100000000000000 : ℝ)^7
        have hw : |(544883321/1250000000 : ℝ)|=(544883321/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(324821577/500000000 : ℝ)|^9 ≤ (2297277138503/4000000000000 : ℝ)^7
        have hw : |(324821577/500000000 : ℝ)|=(324821577/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-356820637/2500000000 : ℝ)|^9 ≤ (4091771524937/50000000000000 : ℝ)^7
        have hw : |(-356820637/2500000000 : ℝ)|=(356820637/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311053_s3_s3_13 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (3195730849/5000000000 : ℝ)*x 0 + (47173073/125000000 : ℝ)*x 1 + (28865211/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3195730849/5000000000 : ℝ)^9 ≤ (56241563832041/100000000000000 : ℝ)^7 := by
    have hnat : (3195730849 : ℕ)^9*100000000000000^7 ≤ 56241563832041^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3195730849 5000000000 56241563832041 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (47173073/125000000 : ℝ)^9 ≤ (28567046566147/100000000000000 : ℝ)^7 := by
    have hnat : (47173073 : ℕ)^9*100000000000000^7 ≤ 28567046566147^7*125000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      47173073 125000000 28567046566147 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (28865211/125000000 : ℝ)^9 ≤ (3038277918247/20000000000000 : ℝ)^7 := by
    have hnat : (28865211 : ℕ)^9*20000000000000^7 ≤ 3038277918247^7*125000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      28865211 125000000 3038277918247 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3195730849/5000000000 : ℝ), (47173073/125000000 : ℝ), (28865211/125000000 : ℝ)] ![(56241563832041/100000000000000 : ℝ), (28567046566147/100000000000000 : ℝ), (3038277918247/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3195730849/5000000000 : ℝ)|^9 ≤ (56241563832041/100000000000000 : ℝ)^7
        have hw : |(3195730849/5000000000 : ℝ)|=(3195730849/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(47173073/125000000 : ℝ)|^9 ≤ (28567046566147/100000000000000 : ℝ)^7
        have hw : |(47173073/125000000 : ℝ)|=(47173073/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(28865211/125000000 : ℝ)|^9 ≤ (3038277918247/20000000000000 : ℝ)^7
        have hw : |(28865211/125000000 : ℝ)|=(28865211/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311053_s3_s3_14 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (-964182247/5000000000 : ℝ)*x 0 + (618945817/1250000000 : ℝ)*x 1 + (1119882071/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (964182247/5000000000 : ℝ)^9 ≤ (12049178779921/100000000000000 : ℝ)^7 := by
    have hnat : (964182247 : ℕ)^9*100000000000000^7 ≤ 12049178779921^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      964182247 5000000000 12049178779921 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (618945817/1250000000 : ℝ)^9 ≤ (810132808313/2000000000000 : ℝ)^7 := by
    have hnat : (618945817 : ℕ)^9*2000000000000^7 ≤ 810132808313^7*1250000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      618945817 1250000000 810132808313 2000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1119882071/2000000000 : ℝ)^9 ≤ (47444180787923/100000000000000 : ℝ)^7 := by
    have hnat : (1119882071 : ℕ)^9*100000000000000^7 ≤ 47444180787923^7*2000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1119882071 2000000000 47444180787923 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-964182247/5000000000 : ℝ), (618945817/1250000000 : ℝ), (1119882071/2000000000 : ℝ)] ![(12049178779921/100000000000000 : ℝ), (810132808313/2000000000000 : ℝ), (47444180787923/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-964182247/5000000000 : ℝ)|^9 ≤ (12049178779921/100000000000000 : ℝ)^7
        have hw : |(-964182247/5000000000 : ℝ)|=(964182247/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(618945817/1250000000 : ℝ)|^9 ≤ (810132808313/2000000000000 : ℝ)^7
        have hw : |(618945817/1250000000 : ℝ)|=(618945817/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1119882071/2000000000 : ℝ)|^9 ≤ (47444180787923/100000000000000 : ℝ)^7
        have hw : |(1119882071/2000000000 : ℝ)|=(1119882071/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311053_s3_s3_15 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (4217015551/10000000000 : ℝ)*x 0 + (-58936677/312500000 : ℝ)*x 1 + (631160039/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4217015551/10000000000 : ℝ)^9 ≤ (16475319148279/50000000000000 : ℝ)^7 := by
    have hnat : (4217015551 : ℕ)^9*50000000000000^7 ≤ 16475319148279^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4217015551 10000000000 16475319148279 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (58936677/312500000 : ℝ)^9 ≤ (2341940180471/20000000000000 : ℝ)^7 := by
    have hnat : (58936677 : ℕ)^9*20000000000000^7 ≤ 2341940180471^7*312500000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      58936677 312500000 2341940180471 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (631160039/1000000000 : ℝ)^9 ≤ (5533966078417/10000000000000 : ℝ)^7 := by
    have hnat : (631160039 : ℕ)^9*10000000000000^7 ≤ 5533966078417^7*1000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      631160039 1000000000 5533966078417 10000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4217015551/10000000000 : ℝ), (-58936677/312500000 : ℝ), (631160039/1000000000 : ℝ)] ![(16475319148279/50000000000000 : ℝ), (2341940180471/20000000000000 : ℝ), (5533966078417/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4217015551/10000000000 : ℝ)|^9 ≤ (16475319148279/50000000000000 : ℝ)^7
        have hw : |(4217015551/10000000000 : ℝ)|=(4217015551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-58936677/312500000 : ℝ)|^9 ≤ (2341940180471/20000000000000 : ℝ)^7
        have hw : |(-58936677/312500000 : ℝ)|=(58936677/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(631160039/1000000000 : ℝ)|^9 ≤ (5533966078417/10000000000000 : ℝ)^7
        have hw : |(631160039/1000000000 : ℝ)|=(631160039/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311053_s3_s3_16 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (5105367327/10000000000 : ℝ)*x 0 + (5764843131/10000000000 : ℝ)*x 1 + (-29708489/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5105367327/10000000000 : ℝ)^9 ≤ (8426284759691/20000000000000 : ℝ)^7 := by
    have hnat : (5105367327 : ℕ)^9*20000000000000^7 ≤ 8426284759691^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5105367327 10000000000 8426284759691 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5764843131/10000000000 : ℝ)^9 ≤ (49253949843541/100000000000000 : ℝ)^7 := by
    have hnat : (5764843131 : ℕ)^9*100000000000000^7 ≤ 49253949843541^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5764843131 10000000000 49253949843541 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (29708489/200000000 : ℝ)^9 ≤ (8614626341197/100000000000000 : ℝ)^7 := by
    have hnat : (29708489 : ℕ)^9*100000000000000^7 ≤ 8614626341197^7*200000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      29708489 200000000 8614626341197 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5105367327/10000000000 : ℝ), (5764843131/10000000000 : ℝ), (-29708489/200000000 : ℝ)] ![(8426284759691/20000000000000 : ℝ), (49253949843541/100000000000000 : ℝ), (8614626341197/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5105367327/10000000000 : ℝ)|^9 ≤ (8426284759691/20000000000000 : ℝ)^7
        have hw : |(5105367327/10000000000 : ℝ)|=(5105367327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5764843131/10000000000 : ℝ)|^9 ≤ (49253949843541/100000000000000 : ℝ)^7
        have hw : |(5764843131/10000000000 : ℝ)|=(5764843131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-29708489/200000000 : ℝ)|^9 ≤ (8614626341197/100000000000000 : ℝ)^7
        have hw : |(-29708489/200000000 : ℝ)|=(29708489/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311053_s3_s3_20 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (1784897657/2500000000 : ℝ)*x 0 + (731918419/2500000000 : ℝ)*x 1 + (558123031/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1784897657/2500000000 : ℝ)^9 ≤ (8105423258947/12500000000000 : ℝ)^7 := by
    have hnat : (1784897657 : ℕ)^9*12500000000000^7 ≤ 8105423258947^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1784897657 2500000000 8105423258947 12500000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (731918419/2500000000 : ℝ)^9 ≤ (20611071643529/100000000000000 : ℝ)^7 := by
    have hnat : (731918419 : ℕ)^9*100000000000000^7 ≤ 20611071643529^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      731918419 2500000000 20611071643529 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (558123031/2500000000 : ℝ)^9 ≤ (3636385569329/25000000000000 : ℝ)^7 := by
    have hnat : (558123031 : ℕ)^9*25000000000000^7 ≤ 3636385569329^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      558123031 2500000000 3636385569329 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1784897657/2500000000 : ℝ), (731918419/2500000000 : ℝ), (558123031/2500000000 : ℝ)] ![(8105423258947/12500000000000 : ℝ), (20611071643529/100000000000000 : ℝ), (3636385569329/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1784897657/2500000000 : ℝ)|^9 ≤ (8105423258947/12500000000000 : ℝ)^7
        have hw : |(1784897657/2500000000 : ℝ)|=(1784897657/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(731918419/2500000000 : ℝ)|^9 ≤ (20611071643529/100000000000000 : ℝ)^7
        have hw : |(731918419/2500000000 : ℝ)|=(731918419/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(558123031/2500000000 : ℝ)|^9 ≤ (3636385569329/25000000000000 : ℝ)^7
        have hw : |(558123031/2500000000 : ℝ)|=(558123031/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311053_s3_s3_21 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (-934343553/5000000000 : ℝ)*x 0 + (1059415253/2000000000 : ℝ)*x 1 + (41438403/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (934343553/5000000000 : ℝ)^9 ≤ (2892971761407/25000000000000 : ℝ)^7 := by
    have hnat : (934343553 : ℕ)^9*25000000000000^7 ≤ 2892971761407^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      934343553 5000000000 2892971761407 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1059415253/2000000000 : ℝ)^9 ≤ (44176309616377/100000000000000 : ℝ)^7 := by
    have hnat : (1059415253 : ℕ)^9*100000000000000^7 ≤ 44176309616377^7*2000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1059415253 2000000000 44176309616377 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (41438403/78125000 : ℝ)^9 ≤ (1382868853781/3125000000000 : ℝ)^7 := by
    have hnat : (41438403 : ℕ)^9*3125000000000^7 ≤ 1382868853781^7*78125000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41438403 78125000 1382868853781 3125000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-934343553/5000000000 : ℝ), (1059415253/2000000000 : ℝ), (41438403/78125000 : ℝ)] ![(2892971761407/25000000000000 : ℝ), (44176309616377/100000000000000 : ℝ), (1382868853781/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-934343553/5000000000 : ℝ)|^9 ≤ (2892971761407/25000000000000 : ℝ)^7
        have hw : |(-934343553/5000000000 : ℝ)|=(934343553/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1059415253/2000000000 : ℝ)|^9 ≤ (44176309616377/100000000000000 : ℝ)^7
        have hw : |(1059415253/2000000000 : ℝ)|=(1059415253/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(41438403/78125000 : ℝ)|^9 ≤ (1382868853781/3125000000000 : ℝ)^7
        have hw : |(41438403/78125000 : ℝ)|=(41438403/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311053_s3_s3_22 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (257419771/500000000 : ℝ)*x 0 + (-310068421/2000000000 : ℝ)*x 1 + (5678711049/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (257419771/500000000 : ℝ)^9 ≤ (42588509085193/100000000000000 : ℝ)^7 := by
    have hnat : (257419771 : ℕ)^9*100000000000000^7 ≤ 42588509085193^7*500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      257419771 500000000 42588509085193 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (310068421/2000000000 : ℝ)^9 ≤ (9101670842703/100000000000000 : ℝ)^7 := by
    have hnat : (310068421 : ℕ)^9*100000000000000^7 ≤ 9101670842703^7*2000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      310068421 2000000000 9101670842703 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5678711049/10000000000 : ℝ)^9 ≤ (24154910025893/50000000000000 : ℝ)^7 := by
    have hnat : (5678711049 : ℕ)^9*50000000000000^7 ≤ 24154910025893^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5678711049 10000000000 24154910025893 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(257419771/500000000 : ℝ), (-310068421/2000000000 : ℝ), (5678711049/10000000000 : ℝ)] ![(42588509085193/100000000000000 : ℝ), (9101670842703/100000000000000 : ℝ), (24154910025893/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(257419771/500000000 : ℝ)|^9 ≤ (42588509085193/100000000000000 : ℝ)^7
        have hw : |(257419771/500000000 : ℝ)|=(257419771/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-310068421/2000000000 : ℝ)|^9 ≤ (9101670842703/100000000000000 : ℝ)^7
        have hw : |(-310068421/2000000000 : ℝ)|=(310068421/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5678711049/10000000000 : ℝ)|^9 ≤ (24154910025893/50000000000000 : ℝ)^7
        have hw : |(5678711049/10000000000 : ℝ)|=(5678711049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311053_s3_s3_23 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (841145361/2000000000 : ℝ)*x 0 + (1603336389/2500000000 : ℝ)*x 1 + (-1754839117/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (841145361/2000000000 : ℝ)^9 ≤ (16418636180197/50000000000000 : ℝ)^7 := by
    have hnat : (841145361 : ℕ)^9*50000000000000^7 ≤ 16418636180197^7*2000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      841145361 2000000000 16418636180197 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1603336389/2500000000 : ℝ)^9 ≤ (11297854106817/20000000000000 : ℝ)^7 := by
    have hnat : (1603336389 : ℕ)^9*20000000000000^7 ≤ 11297854106817^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1603336389 2500000000 11297854106817 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1754839117/10000000000 : ℝ)^9 ≤ (10673457093003/100000000000000 : ℝ)^7 := by
    have hnat : (1754839117 : ℕ)^9*100000000000000^7 ≤ 10673457093003^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1754839117 10000000000 10673457093003 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(841145361/2000000000 : ℝ), (1603336389/2500000000 : ℝ), (-1754839117/10000000000 : ℝ)] ![(16418636180197/50000000000000 : ℝ), (11297854106817/20000000000000 : ℝ), (10673457093003/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(841145361/2000000000 : ℝ)|^9 ≤ (16418636180197/50000000000000 : ℝ)^7
        have hw : |(841145361/2000000000 : ℝ)|=(841145361/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1603336389/2500000000 : ℝ)|^9 ≤ (11297854106817/20000000000000 : ℝ)^7
        have hw : |(1603336389/2500000000 : ℝ)|=(1603336389/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1754839117/10000000000 : ℝ)|^9 ≤ (10673457093003/100000000000000 : ℝ)^7
        have hw : |(-1754839117/10000000000 : ℝ)|=(1754839117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311053_s3_s3_27 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (7203484311/10000000000 : ℝ)*x 0 + (2542762531/10000000000 : ℝ)*x 1 + (254509469/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7203484311/10000000000 : ℝ)^9 ≤ (32795216997093/50000000000000 : ℝ)^7 := by
    have hnat : (7203484311 : ℕ)^9*50000000000000^7 ≤ 32795216997093^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7203484311 10000000000 32795216997093 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2542762531/10000000000 : ℝ)^9 ≤ (429866087159/2500000000000 : ℝ)^7 := by
    have hnat : (2542762531 : ℕ)^9*2500000000000^7 ≤ 429866087159^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2542762531 10000000000 429866087159 2500000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (254509469/1000000000 : ℝ)^9 ≤ (172149225027/1000000000000 : ℝ)^7 := by
    have hnat : (254509469 : ℕ)^9*1000000000000^7 ≤ 172149225027^7*1000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      254509469 1000000000 172149225027 1000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7203484311/10000000000 : ℝ), (2542762531/10000000000 : ℝ), (254509469/1000000000 : ℝ)] ![(32795216997093/50000000000000 : ℝ), (429866087159/2500000000000 : ℝ), (172149225027/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7203484311/10000000000 : ℝ)|^9 ≤ (32795216997093/50000000000000 : ℝ)^7
        have hw : |(7203484311/10000000000 : ℝ)|=(7203484311/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2542762531/10000000000 : ℝ)|^9 ≤ (429866087159/2500000000000 : ℝ)^7
        have hw : |(2542762531/10000000000 : ℝ)|=(2542762531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(254509469/1000000000 : ℝ)|^9 ≤ (172149225027/1000000000000 : ℝ)^7
        have hw : |(254509469/1000000000 : ℝ)|=(254509469/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c311053_s3 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (41087/25000 : ℝ) (89829/50000 : ℝ) (19517/25000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]])
    (hprev2 : (0 : ℝ) ≤ ((9021/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(9021/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(52157/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(52157/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(5057/10000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(5057/10000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((736/3125 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(736/3125 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(28111/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(28111/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(6803/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(6803/25000 : ℝ)*X 1 2) := by
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
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
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
  have base49 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
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
  rcases hprev2 with ⟨ratio_s2_0,ratio_s2_1,ratio_s2_2⟩
  have s3_pow0 : (9021/20000 : ℝ) ^ (71/16 : ℝ) ≤ (182600543814075751/6250000000000000000 : ℝ) := by
    have hpowers : (9021/20000 : ℝ)^71 ≤ (182600543814075751/6250000000000000000 : ℝ)^16 := by
      have hnat : (9021 : ℕ)^71*6250000000000000000^16 ≤ 182600543814075751^16*20000^71 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9021 20000 182600543814075751 6250000000000000000 71 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9021/20000 : ℝ)) (X := (182600543814075751/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have s3_corner0a : (6432600543814075751/6250000000000000000 : ℝ) ≤ (10065106649512649/10000000000000000 : ℝ) ^ (71/16 : ℝ) := by
    have hpowers : (6432600543814075751/6250000000000000000 : ℝ)^16 ≤ (10065106649512649/10000000000000000 : ℝ)^71 := by
      have hnat : (6432600543814075751 : ℕ)^16*10000000000000000^71 ≤ 10065106649512649^71*6250000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6432600543814075751 6250000000000000000 10065106649512649 10000000000000000 16 71 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10065106649512649/10000000000000000 : ℝ)) (X := (6432600543814075751/6250000000000000000 : ℝ)) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have s3_corner0b : (3307600543814075751/3125000000000000000 : ℝ) ≤ (10128796986915803/10000000000000000 : ℝ) ^ (71/16 : ℝ) := by
    have hpowers : (3307600543814075751/3125000000000000000 : ℝ)^16 ≤ (10128796986915803/10000000000000000 : ℝ)^71 := by
      have hnat : (3307600543814075751 : ℕ)^16*10000000000000000^71 ≤ 10128796986915803^71*3125000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3307600543814075751 3125000000000000000 10128796986915803 10000000000000000 16 71 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10128796986915803/10000000000000000 : ℝ)) (X := (3307600543814075751/3125000000000000000 : ℝ)) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have major_s3_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(65106649512649/4510500000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(10615056233859/751750000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (71/16 : ℝ)) (rho := (9021/20000 : ℝ)) (alpha := (65106649512649/4510500000000000 : ℝ)) (beta := (10615056233859/751750000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow0,s3_corner0a]) (by linarith only [s3_pow0,s3_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (9021/20000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(65106649512649/4510500000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(10615056233859/751750000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s3_pow1 : (52157/100000 : ℝ) ^ (71/16 : ℝ) ≤ (556640341238393387/10000000000000000000 : ℝ) := by
    have hpowers : (52157/100000 : ℝ)^71 ≤ (556640341238393387/10000000000000000000 : ℝ)^16 := by
      have hnat : (52157 : ℕ)^71*10000000000000000000^16 ≤ 556640341238393387^16*100000^71 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52157 100000 556640341238393387 10000000000000000000 71 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (52157/100000 : ℝ)) (X := (556640341238393387/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have s3_corner1a : (10556640341238393387/10000000000000000000 : ℝ) ≤ (10122821340515053/10000000000000000 : ℝ) ^ (71/16 : ℝ) := by
    have hpowers : (10556640341238393387/10000000000000000000 : ℝ)^16 ≤ (10122821340515053/10000000000000000 : ℝ)^71 := by
      have hnat : (10556640341238393387 : ℕ)^16*10000000000000000^71 ≤ 10122821340515053^71*10000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10556640341238393387 10000000000000000000 10122821340515053 10000000000000000 16 71 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10122821340515053/10000000000000000 : ℝ)) (X := (10556640341238393387/10000000000000000000 : ℝ)) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have s3_corner1b : (5556640341238393387/5000000000000000000 : ℝ) ≤ (5120361927454177/5000000000000000 : ℝ) ^ (71/16 : ℝ) := by
    have hpowers : (5556640341238393387/5000000000000000000 : ℝ)^16 ≤ (5120361927454177/5000000000000000 : ℝ)^71 := by
      have hnat : (5556640341238393387 : ℕ)^16*5000000000000000^71 ≤ 5120361927454177^71*5000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5556640341238393387 5000000000000000000 5120361927454177 5000000000000000 16 71 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5120361927454177/5000000000000000 : ℝ)) (X := (5556640341238393387/5000000000000000000 : ℝ)) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have major_s3_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(122821340515053/5215700000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(117902514393301/5215700000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (71/16 : ℝ)) (rho := (52157/100000 : ℝ)) (alpha := (122821340515053/5215700000000000 : ℝ)) (beta := (117902514393301/5215700000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow1,s3_corner1a]) (by linarith only [s3_pow1,s3_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (52157/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(122821340515053/5215700000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(117902514393301/5215700000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s3_pow2 : (5057/10000 : ℝ) ^ (71/16 : ℝ) ≤ (4853164160175473007/100000000000000000000 : ℝ) := by
    have hpowers : (5057/10000 : ℝ)^71 ≤ (4853164160175473007/100000000000000000000 : ℝ)^16 := by
      have hnat : (5057 : ℕ)^71*100000000000000000000^16 ≤ 4853164160175473007^16*10000^71 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5057 10000 4853164160175473007 100000000000000000000 71 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5057/10000 : ℝ)) (X := (4853164160175473007/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have s3_corner2a : (104853164160175473007/100000000000000000000 : ℝ) ≤ (5053684179587453/5000000000000000 : ℝ) ^ (71/16 : ℝ) := by
    have hpowers : (104853164160175473007/100000000000000000000 : ℝ)^16 ≤ (5053684179587453/5000000000000000 : ℝ)^71 := by
      have hnat : (104853164160175473007 : ℕ)^16*5000000000000000^71 ≤ 5053684179587453^71*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        104853164160175473007 100000000000000000000 5053684179587453 5000000000000000 16 71 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5053684179587453/5000000000000000 : ℝ)) (X := (104853164160175473007/100000000000000000000 : ℝ)) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have s3_corner2b : (54853164160175473007/50000000000000000000 : ℝ) ≤ (638184587410283/625000000000000 : ℝ) ^ (71/16 : ℝ) := by
    have hpowers : (54853164160175473007/50000000000000000000 : ℝ)^16 ≤ (638184587410283/625000000000000 : ℝ)^71 := by
      have hnat : (54853164160175473007 : ℕ)^16*625000000000000^71 ≤ 638184587410283^71*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        54853164160175473007 50000000000000000000 638184587410283 625000000000000 16 71 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (638184587410283/625000000000000 : ℝ)) (X := (54853164160175473007/50000000000000000000 : ℝ)) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have major_s3_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(53684179587453/2528500000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(51792519694811/2528500000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (71/16 : ℝ)) (rho := (5057/10000 : ℝ)) (alpha := (53684179587453/2528500000000000 : ℝ)) (beta := (51792519694811/2528500000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow2,s3_corner2a]) (by linarith only [s3_pow2,s3_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (5057/10000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(53684179587453/2528500000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(51792519694811/2528500000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s3_0 : ((-2507749043/10000000000 : ℝ)*X 0 0+(201766033/400000000 : ℝ)*X 0 1+(5057682173/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c311053_s3_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_1 : ((1123318243/2500000000 : ℝ)*X 1 0+(-505554039/2500000000 : ℝ)*X 1 1+(5962892607/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c311053_s3_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_2 : ((4509883959/10000000000 : ℝ)*X 2 0+(297791861/500000000 : ℝ)*X 2 1+(-2010936891/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c311053_s3_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_6 : ((3242114267/5000000000 : ℝ)*X 0 0+(1510009191/5000000000 : ℝ)*X 0 1+(187417943/625000000 : ℝ)*X 0 2+(3242114267/5000000000 : ℝ)*X 1 0+(1510009191/5000000000 : ℝ)*X 1 1+(187417943/625000000 : ℝ)*X 1 2+(3242114267/5000000000 : ℝ)*X 2 0+(1510009191/5000000000 : ℝ)*X 2 1+(187417943/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c311053_s3_s3_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_7 : ((-1236470557/5000000000 : ℝ)*X 0 0+(4452157233/10000000000 : ℝ)*X 0 1+(1414387889/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c311053_s3_s3_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_8 : ((2171208853/5000000000 : ℝ)*X 1 0+(-443466973/2500000000 : ℝ)*X 1 1+(6278050117/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c311053_s3_s3_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_9 : ((544883321/1250000000 : ℝ)*X 2 0+(324821577/500000000 : ℝ)*X 2 1+(-356820637/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c311053_s3_s3_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_13 : ((3195730849/5000000000 : ℝ)*X 0 0+(47173073/125000000 : ℝ)*X 0 1+(28865211/125000000 : ℝ)*X 0 2+(3195730849/5000000000 : ℝ)*X 1 0+(47173073/125000000 : ℝ)*X 1 1+(28865211/125000000 : ℝ)*X 1 2+(3195730849/5000000000 : ℝ)*X 2 0+(47173073/125000000 : ℝ)*X 2 1+(28865211/125000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c311053_s3_s3_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_14 : ((-964182247/5000000000 : ℝ)*X 0 0+(618945817/1250000000 : ℝ)*X 0 1+(1119882071/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c311053_s3_s3_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_15 : ((4217015551/10000000000 : ℝ)*X 1 0+(-58936677/312500000 : ℝ)*X 1 1+(631160039/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c311053_s3_s3_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_16 : ((5105367327/10000000000 : ℝ)*X 2 0+(5764843131/10000000000 : ℝ)*X 2 1+(-29708489/200000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c311053_s3_s3_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_20 : ((1784897657/2500000000 : ℝ)*X 0 0+(731918419/2500000000 : ℝ)*X 0 1+(558123031/2500000000 : ℝ)*X 0 2+(1784897657/2500000000 : ℝ)*X 1 0+(731918419/2500000000 : ℝ)*X 1 1+(558123031/2500000000 : ℝ)*X 1 2+(1784897657/2500000000 : ℝ)*X 2 0+(731918419/2500000000 : ℝ)*X 2 1+(558123031/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c311053_s3_s3_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_21 : ((-934343553/5000000000 : ℝ)*X 0 0+(1059415253/2000000000 : ℝ)*X 0 1+(41438403/78125000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c311053_s3_s3_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_22 : ((257419771/500000000 : ℝ)*X 1 0+(-310068421/2000000000 : ℝ)*X 1 1+(5678711049/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c311053_s3_s3_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_23 : ((841145361/2000000000 : ℝ)*X 2 0+(1603336389/2500000000 : ℝ)*X 2 1+(-1754839117/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c311053_s3_s3_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_27 : ((7203484311/10000000000 : ℝ)*X 0 0+(2542762531/10000000000 : ℝ)*X 0 1+(254509469/1000000000 : ℝ)*X 0 2+(7203484311/10000000000 : ℝ)*X 1 0+(2542762531/10000000000 : ℝ)*X 1 1+(254509469/1000000000 : ℝ)*X 1 2+(7203484311/10000000000 : ℝ)*X 2 0+(2542762531/10000000000 : ℝ)*X 2 1+(254509469/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c311053_s3_s3_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s3_0 : (0 : ℝ) ≤ ((736/3125 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(736/3125 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (3160994511338875788850480337769/198280038160750000000000000000000000 : ℝ) := by norm_num
    linear_combination (416305317557/1000000000000 : ℝ)*(base49) + (1093684691193/1000000000000 : ℝ)*(base59) + (1048736934627/125000000000 : ℝ)*(major_s3_0) + (1048736934627/125000000000 : ℝ)*(major_s3_1) + (1048736934627/125000000000 : ℝ)*(major_s3_2) + (25109727/200000000000 : ℝ)*(sp_s3_0) + (30467117/1000000000000 : ℝ)*(sp_s3_6) + (5837331904087/500000000000 : ℝ)*(sp_s3_7) + (5837186607159/500000000000 : ℝ)*(sp_s3_8) + (11674463151209/1000000000000 : ℝ)*(sp_s3_9) + (5104926987197/1000000000000 : ℝ)*(sp_s3_13) + (38828881/1000000000000 : ℝ)*(sp_s3_14) + (454971373/1000000000000 : ℝ)*(sp_s3_15) + (182517241/500000000000 : ℝ)*(sp_s3_23) + (2552478727157/500000000000 : ℝ)*(f.failure) + (11674828185691/1000000000000 : ℝ)*(f.sum) + (8086559793703562217/65939487250000000000000000000000 : ℝ)*base62 + (695429940768037/1264250000000000000000000000 : ℝ)*base65 + (128779890098621/1303925000000000000000000000 : ℝ)*base67 + (214557559681251/1264250000000000000000000000 : ℝ)*base68 + (659952258723954691/1900799875000000000000000000000 : ℝ)*base71 + (50020152787089/187937500000000000000000000 : ℝ)*base72 + (223306862724143/1303925000000000000000000000 : ℝ)*base74 + (78686796033493/375875000000000000000000000 : ℝ)*base76 + (2986980718883215361/19604512375000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base80 + (341/12500000000000000 : ℝ)*base86 + (341/12500000000000000 : ℝ)*base88 + (341/12500000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s3_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(28111/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(28111/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1781379188612771680865460229/123002505062500000000000000000000 : ℝ) := by norm_num
    linear_combination (48449/40000000000 : ℝ)*(base39) + (128560266323/250000000000 : ℝ)*(base49) + (10079965767/15625000000 : ℝ)*(base59) + (4122009130139/500000000000 : ℝ)*(major_s3_0) + (4122009130139/500000000000 : ℝ)*(major_s3_1) + (4122009130139/500000000000 : ℝ)*(major_s3_2) + (28849841/500000000000 : ℝ)*(sp_s3_1) + (25802281/1000000000000 : ℝ)*(sp_s3_2) + (81921877/1000000000000 : ℝ)*(sp_s3_7) + (11471753492387/1000000000000 : ℝ)*(sp_s3_14) + (5735888857291/500000000000 : ℝ)*(sp_s3_15) + (11471809611983/1000000000000 : ℝ)*(sp_s3_16) + (627005091757/125000000000 : ℝ)*(sp_s3_20) + (77772371/500000000000 : ℝ)*(sp_s3_27) + (5016196278797/1000000000000 : ℝ)*(f.failure) + (1433979426783/125000000000 : ℝ)*(f.sum) + (3530158273990142217/8242435906250000000000000000000 : ℝ)*base62 + (31259462116119/79015625000000000000000000 : ℝ)*base64 + (32607654962557/81495312500000000000000000 : ℝ)*base66 + (494463928014333/1264250000000000000000000000 : ℝ)*base68 + (1134148124454486233/2851199812500000000000000000000 : ℝ)*base70 + (355615552741/5873046875000000000000000 : ℝ)*base72 + (976707508999883/2607850000000000000000000000 : ℝ)*base74 + (88996060327141/563812500000000000000000000 : ℝ)*base76 + (2973269513249400719/9802256187500000000000000000000 : ℝ)*base78 + (17661/25000000000000000 : ℝ)*base86 + (17661/25000000000000000 : ℝ)*base88 + (17661/25000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s3_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(6803/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(6803/25000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (25240595992739634486698129/1568360990000000000000000000000 : ℝ) := by norm_num
    linear_combination (122569255961/500000000000 : ℝ)*(base40) + (360506437037/1000000000000 : ℝ)*(base49) + (164224241949/250000000000 : ℝ)*(base59) + (585242221/78125000 : ℝ)*(major_s3_0) + (585242221/78125000 : ℝ)*(major_s3_1) + (585242221/78125000 : ℝ)*(major_s3_2) + (28944159/500000000000 : ℝ)*(sp_s3_0) + (11789643/100000000000 : ℝ)*(sp_s3_2) + (2874081/50000000000 : ℝ)*(sp_s3_9) + (360062609/1000000000000 : ℝ)*(sp_s3_20) + (10424065447611/1000000000000 : ℝ)*(sp_s3_21) + (10424123335929/1000000000000 : ℝ)*(sp_s3_22) + (10423947957879/1000000000000 : ℝ)*(sp_s3_23) + (4557712094521/1000000000000 : ℝ)*(sp_s3_27) + (455807215713/100000000000 : ℝ)*(f.failure) + (10424123335929/1000000000000 : ℝ)*(f.sum) + (303891737562177369/2637579490000000000000000000000 : ℝ)*base63 + (658174506167/6321250000000000000000000 : ℝ)*base64 + (39775257445097/130392500000000000000000000 : ℝ)*base66 + (11755692636863/50570000000000000000000000 : ℝ)*base68 + (168886877482515241/228095985000000000000000000000 : ℝ)*base71 + (23567633383121/30070000000000000000000000 : ℝ)*base72 + (14787234044477/65196250000000000000000000 : ℝ)*base74 + (2928536429837/18042000000000000000000000 : ℝ)*base77 + (628866684266540011/1568360990000000000000000000000 : ℝ)*base78 + (31/2500000000000000 : ℝ)*base87 + (31/2500000000000000 : ℝ)*base89 + (31/2500000000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s3_0,ratio_s3_1,ratio_s3_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (41087/25000 : ℝ) (89829/50000 : ℝ) (19517/25000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]])
    (hprev2 : (0 : ℝ) ≤ ((9021/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(9021/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(52157/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(52157/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(5057/10000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(5057/10000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((736/3125 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(736/3125 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(28111/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(28111/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(6803/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(6803/25000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c311053_s3 p hpa hpb X hX hprev2

#print axioms solution
