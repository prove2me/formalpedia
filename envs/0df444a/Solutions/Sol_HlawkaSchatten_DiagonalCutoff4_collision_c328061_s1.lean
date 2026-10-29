-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c328061_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:22:45.590816+00:00
-- url     : https://prove2.me/submissions/8691a773-c0b4-49e9-b85d-d53d6e6e147b

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
theorem collision_support_c328061_s1_s1_0 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-438256153/2500000000 : ℝ)*x 0 + (4372137497/10000000000 : ℝ)*x 1 + (1431040843/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (438256153/2500000000 : ℝ)^93 ≤ (6104119955853/50000000000000 : ℝ)^77 := by
    have hnat : (438256153 : ℕ)^93*50000000000000^77 ≤ 6104119955853^77*2500000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      438256153 2500000000 6104119955853 50000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4372137497/10000000000 : ℝ)^93 ≤ (7363135299871/20000000000000 : ℝ)^77 := by
    have hnat : (4372137497 : ℕ)^93*20000000000000^77 ≤ 7363135299871^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4372137497 10000000000 7363135299871 20000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1431040843/2500000000 : ℝ)^93 ≤ (25488041787831/50000000000000 : ℝ)^77 := by
    have hnat : (1431040843 : ℕ)^93*50000000000000^77 ≤ 25488041787831^77*2500000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1431040843 2500000000 25488041787831 50000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-438256153/2500000000 : ℝ), (4372137497/10000000000 : ℝ), (1431040843/2500000000 : ℝ)] ![(6104119955853/50000000000000 : ℝ), (7363135299871/20000000000000 : ℝ), (25488041787831/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-438256153/2500000000 : ℝ)|^93 ≤ (6104119955853/50000000000000 : ℝ)^77
        have hw : |(-438256153/2500000000 : ℝ)|=(438256153/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4372137497/10000000000 : ℝ)|^93 ≤ (7363135299871/20000000000000 : ℝ)^77
        have hw : |(4372137497/10000000000 : ℝ)|=(4372137497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1431040843/2500000000 : ℝ)|^93 ≤ (25488041787831/50000000000000 : ℝ)^77
        have hw : |(1431040843/2500000000 : ℝ)|=(1431040843/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328061_s1_s1_1 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4604644923/10000000000 : ℝ)*x 0 + (-351034313/2000000000 : ℝ)*x 1 + (1375130363/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4604644923/10000000000 : ℝ)^93 ≤ (7838643719891/20000000000000 : ℝ)^77 := by
    have hnat : (4604644923 : ℕ)^93*20000000000000^77 ≤ 7838643719891^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4604644923 10000000000 7838643719891 20000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (351034313/2000000000 : ℝ)^93 ≤ (6113150315483/50000000000000 : ℝ)^77 := by
    have hnat : (351034313 : ℕ)^93*50000000000000^77 ≤ 6113150315483^77*2000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      351034313 2000000000 6113150315483 50000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1375130363/2500000000 : ℝ)^93 ≤ (48580480753169/100000000000000 : ℝ)^77 := by
    have hnat : (1375130363 : ℕ)^93*100000000000000^77 ≤ 48580480753169^77*2500000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1375130363 2500000000 48580480753169 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4604644923/10000000000 : ℝ), (-351034313/2000000000 : ℝ), (1375130363/2500000000 : ℝ)] ![(7838643719891/20000000000000 : ℝ), (6113150315483/50000000000000 : ℝ), (48580480753169/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4604644923/10000000000 : ℝ)|^93 ≤ (7838643719891/20000000000000 : ℝ)^77
        have hw : |(4604644923/10000000000 : ℝ)|=(4604644923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-351034313/2000000000 : ℝ)|^93 ≤ (6113150315483/50000000000000 : ℝ)^77
        have hw : |(-351034313/2000000000 : ℝ)|=(351034313/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1375130363/2500000000 : ℝ)|^93 ≤ (48580480753169/100000000000000 : ℝ)^77
        have hw : |(1375130363/2500000000 : ℝ)|=(1375130363/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328061_s1_s1_2 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4642258319/10000000000 : ℝ)*x 0 + (1529262923/2500000000 : ℝ)*x 1 + (-863158457/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4642258319/10000000000 : ℝ)^93 ≤ (39580224141243/100000000000000 : ℝ)^77 := by
    have hnat : (4642258319 : ℕ)^93*100000000000000^77 ≤ 39580224141243^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4642258319 10000000000 39580224141243 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1529262923/2500000000 : ℝ)^93 ≤ (55231555265101/100000000000000 : ℝ)^77 := by
    have hnat : (1529262923 : ℕ)^93*100000000000000^77 ≤ 55231555265101^77*2500000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1529262923 2500000000 55231555265101 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (863158457/10000000000 : ℝ)^93 ≤ (5188220583141/100000000000000 : ℝ)^77 := by
    have hnat : (863158457 : ℕ)^93*100000000000000^77 ≤ 5188220583141^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      863158457 10000000000 5188220583141 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4642258319/10000000000 : ℝ), (1529262923/2500000000 : ℝ), (-863158457/10000000000 : ℝ)] ![(39580224141243/100000000000000 : ℝ), (55231555265101/100000000000000 : ℝ), (5188220583141/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4642258319/10000000000 : ℝ)|^93 ≤ (39580224141243/100000000000000 : ℝ)^77
        have hw : |(4642258319/10000000000 : ℝ)|=(4642258319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1529262923/2500000000 : ℝ)|^93 ≤ (55231555265101/100000000000000 : ℝ)^77
        have hw : |(1529262923/2500000000 : ℝ)|=(1529262923/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-863158457/10000000000 : ℝ)|^93 ≤ (5188220583141/100000000000000 : ℝ)^77
        have hw : |(-863158457/10000000000 : ℝ)|=(863158457/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328061_s1_s1_6 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6545444841/10000000000 : ℝ)*x 0 + (2376632153/10000000000 : ℝ)*x 1 + (725240363/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6545444841/10000000000 : ℝ)^93 ≤ (14984172679823/25000000000000 : ℝ)^77 := by
    have hnat : (6545444841 : ℕ)^93*25000000000000^77 ≤ 14984172679823^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6545444841 10000000000 14984172679823 25000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2376632153/10000000000 : ℝ)^93 ≤ (8815800067389/50000000000000 : ℝ)^77 := by
    have hnat : (2376632153 : ℕ)^93*50000000000000^77 ≤ 8815800067389^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2376632153 10000000000 8815800067389 50000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (725240363/2500000000 : ℝ)^93 ≤ (11215854562693/50000000000000 : ℝ)^77 := by
    have hnat : (725240363 : ℕ)^93*50000000000000^77 ≤ 11215854562693^77*2500000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      725240363 2500000000 11215854562693 50000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6545444841/10000000000 : ℝ), (2376632153/10000000000 : ℝ), (725240363/2500000000 : ℝ)] ![(14984172679823/25000000000000 : ℝ), (8815800067389/50000000000000 : ℝ), (11215854562693/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6545444841/10000000000 : ℝ)|^93 ≤ (14984172679823/25000000000000 : ℝ)^77
        have hw : |(6545444841/10000000000 : ℝ)|=(6545444841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2376632153/10000000000 : ℝ)|^93 ≤ (8815800067389/50000000000000 : ℝ)^77
        have hw : |(2376632153/10000000000 : ℝ)|=(2376632153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(725240363/2500000000 : ℝ)|^93 ≤ (11215854562693/50000000000000 : ℝ)^77
        have hw : |(725240363/2500000000 : ℝ)|=(725240363/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328061_s1_s1_7 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-895667799/5000000000 : ℝ)*x 0 + (4057358511/10000000000 : ℝ)*x 1 + (5988254651/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (895667799/5000000000 : ℝ)^93 ≤ (2506241650011/20000000000000 : ℝ)^77 := by
    have hnat : (895667799 : ℕ)^93*20000000000000^77 ≤ 2506241650011^77*5000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      895667799 5000000000 2506241650011 20000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4057358511/10000000000 : ℝ)^93 ≤ (33638716116649/100000000000000 : ℝ)^77 := by
    have hnat : (4057358511 : ℕ)^93*100000000000000^77 ≤ 33638716116649^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4057358511 10000000000 33638716116649 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5988254651/10000000000 : ℝ)^93 ≤ (10766015124251/20000000000000 : ℝ)^77 := by
    have hnat : (5988254651 : ℕ)^93*20000000000000^77 ≤ 10766015124251^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5988254651 10000000000 10766015124251 20000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-895667799/5000000000 : ℝ), (4057358511/10000000000 : ℝ), (5988254651/10000000000 : ℝ)] ![(2506241650011/20000000000000 : ℝ), (33638716116649/100000000000000 : ℝ), (10766015124251/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-895667799/5000000000 : ℝ)|^93 ≤ (2506241650011/20000000000000 : ℝ)^77
        have hw : |(-895667799/5000000000 : ℝ)|=(895667799/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4057358511/10000000000 : ℝ)|^93 ≤ (33638716116649/100000000000000 : ℝ)^77
        have hw : |(4057358511/10000000000 : ℝ)|=(4057358511/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5988254651/10000000000 : ℝ)|^93 ≤ (10766015124251/20000000000000 : ℝ)^77
        have hw : |(5988254651/10000000000 : ℝ)|=(5988254651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328061_s1_s1_8 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (273315231/625000000 : ℝ)*x 0 + (-1400735563/10000000000 : ℝ)*x 1 + (2995714917/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (273315231/625000000 : ℝ)^93 ≤ (4603111619879/12500000000000 : ℝ)^77 := by
    have hnat : (273315231 : ℕ)^93*12500000000000^77 ≤ 4603111619879^77*625000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      273315231 625000000 4603111619879 12500000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1400735563/10000000000 : ℝ)^93 ≤ (4655277991403/50000000000000 : ℝ)^77 := by
    have hnat : (1400735563 : ℕ)^93*50000000000000^77 ≤ 4655277991403^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1400735563 10000000000 4655277991403 50000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2995714917/5000000000 : ℝ)^93 ≤ (13466137761679/25000000000000 : ℝ)^77 := by
    have hnat : (2995714917 : ℕ)^93*25000000000000^77 ≤ 13466137761679^77*5000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2995714917 5000000000 13466137761679 25000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(273315231/625000000 : ℝ), (-1400735563/10000000000 : ℝ), (2995714917/5000000000 : ℝ)] ![(4603111619879/12500000000000 : ℝ), (4655277991403/50000000000000 : ℝ), (13466137761679/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(273315231/625000000 : ℝ)|^93 ≤ (4603111619879/12500000000000 : ℝ)^77
        have hw : |(273315231/625000000 : ℝ)|=(273315231/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1400735563/10000000000 : ℝ)|^93 ≤ (4655277991403/50000000000000 : ℝ)^77
        have hw : |(-1400735563/10000000000 : ℝ)|=(1400735563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2995714917/5000000000 : ℝ)|^93 ≤ (13466137761679/25000000000000 : ℝ)^77
        have hw : |(2995714917/5000000000 : ℝ)|=(2995714917/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328061_s1_s1_9 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1102692939/2500000000 : ℝ)*x 0 + (6622497363/10000000000 : ℝ)*x 1 + (-98054899/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1102692939/2500000000 : ℝ)^93 ≤ (37208956072779/100000000000000 : ℝ)^77 := by
    have hnat : (1102692939 : ℕ)^93*100000000000000^77 ≤ 37208956072779^77*2500000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1102692939 2500000000 37208956072779 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6622497363/10000000000 : ℝ)^93 ≤ (30394956194457/50000000000000 : ℝ)^77 := by
    have hnat : (6622497363 : ℕ)^93*50000000000000^77 ≤ 30394956194457^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6622497363 10000000000 30394956194457 50000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (98054899/2500000000 : ℝ)^93 ≤ (2001131524337/100000000000000 : ℝ)^77 := by
    have hnat : (98054899 : ℕ)^93*100000000000000^77 ≤ 2001131524337^77*2500000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      98054899 2500000000 2001131524337 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1102692939/2500000000 : ℝ), (6622497363/10000000000 : ℝ), (-98054899/2500000000 : ℝ)] ![(37208956072779/100000000000000 : ℝ), (30394956194457/50000000000000 : ℝ), (2001131524337/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1102692939/2500000000 : ℝ)|^93 ≤ (37208956072779/100000000000000 : ℝ)^77
        have hw : |(1102692939/2500000000 : ℝ)|=(1102692939/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6622497363/10000000000 : ℝ)|^93 ≤ (30394956194457/50000000000000 : ℝ)^77
        have hw : |(6622497363/10000000000 : ℝ)|=(6622497363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-98054899/2500000000 : ℝ)|^93 ≤ (2001131524337/100000000000000 : ℝ)^77
        have hw : |(-98054899/2500000000 : ℝ)|=(98054899/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328061_s1_s1_13 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6655007061/10000000000 : ℝ)*x 0 + (762967921/2500000000 : ℝ)*x 1 + (2079025033/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6655007061/10000000000 : ℝ)^93 ≤ (61150520955537/100000000000000 : ℝ)^77 := by
    have hnat : (6655007061 : ℕ)^93*100000000000000^77 ≤ 61150520955537^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6655007061 10000000000 61150520955537 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (762967921/2500000000 : ℝ)^93 ≤ (11924307345137/50000000000000 : ℝ)^77 := by
    have hnat : (762967921 : ℕ)^93*50000000000000^77 ≤ 11924307345137^77*2500000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      762967921 2500000000 11924307345137 50000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2079025033/10000000000 : ℝ)^93 ≤ (15000864338303/100000000000000 : ℝ)^77 := by
    have hnat : (2079025033 : ℕ)^93*100000000000000^77 ≤ 15000864338303^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2079025033 10000000000 15000864338303 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6655007061/10000000000 : ℝ), (762967921/2500000000 : ℝ), (2079025033/10000000000 : ℝ)] ![(61150520955537/100000000000000 : ℝ), (11924307345137/50000000000000 : ℝ), (15000864338303/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6655007061/10000000000 : ℝ)|^93 ≤ (61150520955537/100000000000000 : ℝ)^77
        have hw : |(6655007061/10000000000 : ℝ)|=(6655007061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(762967921/2500000000 : ℝ)|^93 ≤ (11924307345137/50000000000000 : ℝ)^77
        have hw : |(762967921/2500000000 : ℝ)|=(762967921/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2079025033/10000000000 : ℝ)|^93 ≤ (15000864338303/100000000000000 : ℝ)^77
        have hw : |(2079025033/10000000000 : ℝ)|=(2079025033/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328061_s1_s1_14 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-541843829/5000000000 : ℝ)*x 0 + (1154913641/2500000000 : ℝ)*x 1 + (1496907769/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (541843829/5000000000 : ℝ)^93 ≤ (1365823940281/20000000000000 : ℝ)^77 := by
    have hnat : (541843829 : ℕ)^93*20000000000000^77 ≤ 1365823940281^77*5000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      541843829 5000000000 1365823940281 20000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1154913641/2500000000 : ℝ)^93 ≤ (2459223428601/6250000000000 : ℝ)^77 := by
    have hnat : (1154913641 : ℕ)^93*6250000000000^77 ≤ 2459223428601^77*2500000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1154913641 2500000000 2459223428601 6250000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1496907769/2500000000 : ℝ)^93 ≤ (26911652714907/50000000000000 : ℝ)^77 := by
    have hnat : (1496907769 : ℕ)^93*50000000000000^77 ≤ 26911652714907^77*2500000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1496907769 2500000000 26911652714907 50000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-541843829/5000000000 : ℝ), (1154913641/2500000000 : ℝ), (1496907769/2500000000 : ℝ)] ![(1365823940281/20000000000000 : ℝ), (2459223428601/6250000000000 : ℝ), (26911652714907/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-541843829/5000000000 : ℝ)|^93 ≤ (1365823940281/20000000000000 : ℝ)^77
        have hw : |(-541843829/5000000000 : ℝ)|=(541843829/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1154913641/2500000000 : ℝ)|^93 ≤ (2459223428601/6250000000000 : ℝ)^77
        have hw : |(1154913641/2500000000 : ℝ)|=(1154913641/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1496907769/2500000000 : ℝ)|^93 ≤ (26911652714907/50000000000000 : ℝ)^77
        have hw : |(1496907769/2500000000 : ℝ)|=(1496907769/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328061_s1_s1_15 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1080626369/2500000000 : ℝ)*x 0 + (-36630549/250000000 : ℝ)*x 1 + (2995403643/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1080626369/2500000000 : ℝ)^93 ≤ (36311504066883/100000000000000 : ℝ)^77 := by
    have hnat : (1080626369 : ℕ)^93*100000000000000^77 ≤ 36311504066883^77*2500000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1080626369 2500000000 36311504066883 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (36630549/250000000 : ℝ)^93 ≤ (614419041241/6250000000000 : ℝ)^77 := by
    have hnat : (36630549 : ℕ)^93*6250000000000^77 ≤ 614419041241^77*250000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      36630549 250000000 614419041241 6250000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2995403643/5000000000 : ℝ)^93 ≤ (53857791260771/100000000000000 : ℝ)^77 := by
    have hnat : (2995403643 : ℕ)^93*100000000000000^77 ≤ 53857791260771^77*5000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2995403643 5000000000 53857791260771 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1080626369/2500000000 : ℝ), (-36630549/250000000 : ℝ), (2995403643/5000000000 : ℝ)] ![(36311504066883/100000000000000 : ℝ), (614419041241/6250000000000 : ℝ), (53857791260771/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1080626369/2500000000 : ℝ)|^93 ≤ (36311504066883/100000000000000 : ℝ)^77
        have hw : |(1080626369/2500000000 : ℝ)|=(1080626369/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-36630549/250000000 : ℝ)|^93 ≤ (614419041241/6250000000000 : ℝ)^77
        have hw : |(-36630549/250000000 : ℝ)|=(36630549/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2995403643/5000000000 : ℝ)|^93 ≤ (53857791260771/100000000000000 : ℝ)^77
        have hw : |(2995403643/5000000000 : ℝ)|=(2995403643/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328061_s1_s1_16 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (666458493/1250000000 : ℝ)*x 0 + (5745897091/10000000000 : ℝ)*x 1 + (-24552741/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (666458493/1250000000 : ℝ)^93 ≤ (4678507962647/10000000000000 : ℝ)^77 := by
    have hnat : (666458493 : ℕ)^93*10000000000000^77 ≤ 4678507962647^77*1250000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      666458493 1250000000 4678507962647 10000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5745897091/10000000000 : ℝ)^93 ≤ (51209941359997/100000000000000 : ℝ)^77 := by
    have hnat : (5745897091 : ℕ)^93*100000000000000^77 ≤ 51209941359997^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5745897091 10000000000 51209941359997 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (24552741/625000000 : ℝ)^93 ≤ (2004978999781/100000000000000 : ℝ)^77 := by
    have hnat : (24552741 : ℕ)^93*100000000000000^77 ≤ 2004978999781^77*625000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      24552741 625000000 2004978999781 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(666458493/1250000000 : ℝ), (5745897091/10000000000 : ℝ), (-24552741/625000000 : ℝ)] ![(4678507962647/10000000000000 : ℝ), (51209941359997/100000000000000 : ℝ), (2004978999781/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(666458493/1250000000 : ℝ)|^93 ≤ (4678507962647/10000000000000 : ℝ)^77
        have hw : |(666458493/1250000000 : ℝ)|=(666458493/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5745897091/10000000000 : ℝ)|^93 ≤ (51209941359997/100000000000000 : ℝ)^77
        have hw : |(5745897091/10000000000 : ℝ)|=(5745897091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-24552741/625000000 : ℝ)|^93 ≤ (2004978999781/100000000000000 : ℝ)^77
        have hw : |(-24552741/625000000 : ℝ)|=(24552741/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328061_s1_s1_20 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1883978913/2500000000 : ℝ)*x 0 + (977344161/5000000000 : ℝ)*x 1 + (2081106767/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1883978913/2500000000 : ℝ)^93 ≤ (71056833968107/100000000000000 : ℝ)^77 := by
    have hnat : (1883978913 : ℕ)^93*100000000000000^77 ≤ 71056833968107^77*2500000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1883978913 2500000000 71056833968107 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (977344161/5000000000 : ℝ)^93 ≤ (870259891161/6250000000000 : ℝ)^77 := by
    have hnat : (977344161 : ℕ)^93*6250000000000^77 ≤ 870259891161^77*5000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      977344161 5000000000 870259891161 6250000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2081106767/10000000000 : ℝ)^93 ≤ (15019007759789/100000000000000 : ℝ)^77 := by
    have hnat : (2081106767 : ℕ)^93*100000000000000^77 ≤ 15019007759789^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2081106767 10000000000 15019007759789 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1883978913/2500000000 : ℝ), (977344161/5000000000 : ℝ), (2081106767/10000000000 : ℝ)] ![(71056833968107/100000000000000 : ℝ), (870259891161/6250000000000 : ℝ), (15019007759789/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1883978913/2500000000 : ℝ)|^93 ≤ (71056833968107/100000000000000 : ℝ)^77
        have hw : |(1883978913/2500000000 : ℝ)|=(1883978913/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(977344161/5000000000 : ℝ)|^93 ≤ (870259891161/6250000000000 : ℝ)^77
        have hw : |(977344161/5000000000 : ℝ)|=(977344161/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2081106767/10000000000 : ℝ)|^93 ≤ (15019007759789/100000000000000 : ℝ)^77
        have hw : |(2081106767/10000000000 : ℝ)|=(2081106767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328061_s1_s1_21 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1086136293/10000000000 : ℝ)*x 0 + (487135853/1000000000 : ℝ)*x 1 + (5745053623/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1086136293/10000000000 : ℝ)^93 ≤ (3423880555633/50000000000000 : ℝ)^77 := by
    have hnat : (1086136293 : ℕ)^93*50000000000000^77 ≤ 3423880555633^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1086136293 10000000000 3423880555633 50000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (487135853/1000000000 : ℝ)^93 ≤ (41951376773071/100000000000000 : ℝ)^77 := by
    have hnat : (487135853 : ℕ)^93*100000000000000^77 ≤ 41951376773071^77*1000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      487135853 1000000000 41951376773071 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5745053623/10000000000 : ℝ)^93 ≤ (2560043104799/5000000000000 : ℝ)^77 := by
    have hnat : (5745053623 : ℕ)^93*5000000000000^77 ≤ 2560043104799^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5745053623 10000000000 2560043104799 5000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1086136293/10000000000 : ℝ), (487135853/1000000000 : ℝ), (5745053623/10000000000 : ℝ)] ![(3423880555633/50000000000000 : ℝ), (41951376773071/100000000000000 : ℝ), (2560043104799/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1086136293/10000000000 : ℝ)|^93 ≤ (3423880555633/50000000000000 : ℝ)^77
        have hw : |(-1086136293/10000000000 : ℝ)|=(1086136293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(487135853/1000000000 : ℝ)|^93 ≤ (41951376773071/100000000000000 : ℝ)^77
        have hw : |(487135853/1000000000 : ℝ)|=(487135853/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5745053623/10000000000 : ℝ)|^93 ≤ (2560043104799/5000000000000 : ℝ)^77
        have hw : |(5745053623/10000000000 : ℝ)|=(5745053623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328061_s1_s1_22 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2645744591/5000000000 : ℝ)*x 0 + (-543276977/5000000000 : ℝ)*x 1 + (5332082337/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2645744591/5000000000 : ℝ)^93 ≤ (46359586830821/100000000000000 : ℝ)^77 := by
    have hnat : (2645744591 : ℕ)^93*100000000000000^77 ≤ 46359586830821^77*5000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2645744591 5000000000 46359586830821 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (543276977/5000000000 : ℝ)^93 ≤ (1712735407159/25000000000000 : ℝ)^77 := by
    have hnat : (543276977 : ℕ)^93*25000000000000^77 ≤ 1712735407159^77*5000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      543276977 5000000000 1712735407159 25000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5332082337/10000000000 : ℝ)^93 ≤ (23394735763119/50000000000000 : ℝ)^77 := by
    have hnat : (5332082337 : ℕ)^93*50000000000000^77 ≤ 23394735763119^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5332082337 10000000000 23394735763119 50000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2645744591/5000000000 : ℝ), (-543276977/5000000000 : ℝ), (5332082337/10000000000 : ℝ)] ![(46359586830821/100000000000000 : ℝ), (1712735407159/25000000000000 : ℝ), (23394735763119/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2645744591/5000000000 : ℝ)|^93 ≤ (46359586830821/100000000000000 : ℝ)^77
        have hw : |(2645744591/5000000000 : ℝ)|=(2645744591/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-543276977/5000000000 : ℝ)|^93 ≤ (1712735407159/25000000000000 : ℝ)^77
        have hw : |(-543276977/5000000000 : ℝ)|=(543276977/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5332082337/10000000000 : ℝ)|^93 ≤ (23394735763119/50000000000000 : ℝ)^77
        have hw : |(5332082337/10000000000 : ℝ)|=(5332082337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328061_s1_s1_23 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4278918819/10000000000 : ℝ)*x 0 + (1629463421/2500000000 : ℝ)*x 1 + (-767018067/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4278918819/10000000000 : ℝ)^93 ≤ (4483716529019/12500000000000 : ℝ)^77 := by
    have hnat : (4278918819 : ℕ)^93*12500000000000^77 ≤ 4483716529019^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4278918819 10000000000 4483716529019 12500000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1629463421/2500000000 : ℝ)^93 ≤ (14907918214163/25000000000000 : ℝ)^77 := by
    have hnat : (1629463421 : ℕ)^93*25000000000000^77 ≤ 14907918214163^77*2500000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1629463421 2500000000 14907918214163 25000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (767018067/10000000000 : ℝ)^93 ≤ (4498594894549/100000000000000 : ℝ)^77 := by
    have hnat : (767018067 : ℕ)^93*100000000000000^77 ≤ 4498594894549^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      767018067 10000000000 4498594894549 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4278918819/10000000000 : ℝ), (1629463421/2500000000 : ℝ), (-767018067/10000000000 : ℝ)] ![(4483716529019/12500000000000 : ℝ), (14907918214163/25000000000000 : ℝ), (4498594894549/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4278918819/10000000000 : ℝ)|^93 ≤ (4483716529019/12500000000000 : ℝ)^77
        have hw : |(4278918819/10000000000 : ℝ)|=(4278918819/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1629463421/2500000000 : ℝ)|^93 ≤ (14907918214163/25000000000000 : ℝ)^77
        have hw : |(1629463421/2500000000 : ℝ)|=(1629463421/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-767018067/10000000000 : ℝ)|^93 ≤ (4498594894549/100000000000000 : ℝ)^77
        have hw : |(-767018067/10000000000 : ℝ)|=(767018067/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328061_s1_s1_27 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (7807467911/10000000000 : ℝ)*x 0 + (346435827/2000000000 : ℝ)*x 1 + (485237171/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7807467911/10000000000 : ℝ)^93 ≤ (18540211128273/25000000000000 : ℝ)^77 := by
    have hnat : (7807467911 : ℕ)^93*25000000000000^77 ≤ 18540211128273^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7807467911 10000000000 18540211128273 25000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (346435827/2000000000 : ℝ)^93 ≤ (1203312201663/10000000000000 : ℝ)^77 := by
    have hnat : (346435827 : ℕ)^93*10000000000000^77 ≤ 1203312201663^77*2000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      346435827 2000000000 1203312201663 10000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (485237171/2500000000 : ℝ)^93 ≤ (690301673051/5000000000000 : ℝ)^77 := by
    have hnat : (485237171 : ℕ)^93*5000000000000^77 ≤ 690301673051^77*2500000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      485237171 2500000000 690301673051 5000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7807467911/10000000000 : ℝ), (346435827/2000000000 : ℝ), (485237171/2500000000 : ℝ)] ![(18540211128273/25000000000000 : ℝ), (1203312201663/10000000000000 : ℝ), (690301673051/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7807467911/10000000000 : ℝ)|^93 ≤ (18540211128273/25000000000000 : ℝ)^77
        have hw : |(7807467911/10000000000 : ℝ)|=(7807467911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(346435827/2000000000 : ℝ)|^93 ≤ (1203312201663/10000000000000 : ℝ)^77
        have hw : |(346435827/2000000000 : ℝ)|=(346435827/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(485237171/2500000000 : ℝ)|^93 ≤ (690301673051/5000000000000 : ℝ)^77
        have hw : |(485237171/2500000000 : ℝ)|=(485237171/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c328061_s1 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (8679/4000 : ℝ) (80697/50000 : ℝ) (82433/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]])
    (hprev0 : (0 : ℝ) ≤ ((62549/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(62549/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(12429/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(12429/20000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(57197/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(57197/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((11641/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(11641/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(29769/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(29769/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(27093/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(27093/100000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (82433/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (82433/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (82433/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (82433/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (82433/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (82433/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base11 : ((1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).2]
  have base13 : ((1 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 2).2]
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
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
  rcases hprev0 with ⟨ratio_s0_0,ratio_s0_1,ratio_s0_2⟩
  have s1_pow0 : (62549/100000 : ℝ) ^ (91/16 : ℝ) ≤ (1386862338581368159/20000000000000000000 : ℝ) := by
    have hpowers : (62549/100000 : ℝ)^91 ≤ (1386862338581368159/20000000000000000000 : ℝ)^16 := by
      have hnat : (62549 : ℕ)^91*20000000000000000000^16 ≤ 1386862338581368159^16*100000^91 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        62549 100000 1386862338581368159 20000000000000000000 91 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (62549/100000 : ℝ)) (X := (1386862338581368159/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (21386862338581368159/20000000000000000000 : ℝ) ≤ (5059289028758487/5000000000000000 : ℝ) ^ (91/16 : ℝ) := by
    have hpowers : (21386862338581368159/20000000000000000000 : ℝ)^16 ≤ (5059289028758487/5000000000000000 : ℝ)^91 := by
      have hnat : (21386862338581368159 : ℕ)^16*5000000000000000^91 ≤ 5059289028758487^91*20000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        21386862338581368159 20000000000000000000 5059289028758487 5000000000000000 16 91 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5059289028758487/5000000000000000 : ℝ)) (X := (21386862338581368159/20000000000000000000 : ℝ)) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (11386862338581368159/10000000000000000000 : ℝ) ≤ (10230979139736803/10000000000000000 : ℝ) ^ (91/16 : ℝ) := by
    have hpowers : (11386862338581368159/10000000000000000000 : ℝ)^16 ≤ (10230979139736803/10000000000000000 : ℝ)^91 := by
      have hnat : (11386862338581368159 : ℕ)^16*10000000000000000^91 ≤ 10230979139736803^91*10000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11386862338581368159 10000000000000000000 10230979139736803 10000000000000000 16 91 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10230979139736803/10000000000000000 : ℝ)) (X := (11386862338581368159/10000000000000000000 : ℝ)) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(59289028758487/3127450000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(112401082219829/6254900000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (91/16 : ℝ)) (rho := (62549/100000 : ℝ)) (alpha := (59289028758487/3127450000000000 : ℝ)) (beta := (112401082219829/6254900000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (62549/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(59289028758487/3127450000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(112401082219829/6254900000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (12429/20000 : ℝ) ^ (91/16 : ℝ) ≤ (1670851018311367889/25000000000000000000 : ℝ) := by
    have hpowers : (12429/20000 : ℝ)^91 ≤ (1670851018311367889/25000000000000000000 : ℝ)^16 := by
      have hnat : (12429 : ℕ)^91*25000000000000000000^16 ≤ 1670851018311367889^16*20000^91 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12429 20000 1670851018311367889 25000000000000000000 91 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (12429/20000 : ℝ)) (X := (1670851018311367889/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (26670851018311367889/25000000000000000000 : ℝ) ≤ (2022879921580671/2000000000000000 : ℝ) ^ (91/16 : ℝ) := by
    have hpowers : (26670851018311367889/25000000000000000000 : ℝ)^16 ≤ (2022879921580671/2000000000000000 : ℝ)^91 := by
      have hnat : (26670851018311367889 : ℕ)^16*2000000000000000^91 ≤ 2022879921580671^91*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26670851018311367889 25000000000000000000 2022879921580671 2000000000000000 16 91 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2022879921580671/2000000000000000 : ℝ)) (X := (26670851018311367889/25000000000000000000 : ℝ)) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (14170851018311367889/12500000000000000000 : ℝ) ≤ (10223037216774821/10000000000000000 : ℝ) ^ (91/16 : ℝ) := by
    have hpowers : (14170851018311367889/12500000000000000000 : ℝ)^16 ≤ (10223037216774821/10000000000000000 : ℝ)^91 := by
      have hnat : (14170851018311367889 : ℕ)^16*10000000000000000^91 ≤ 10223037216774821^91*12500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14170851018311367889 12500000000000000000 10223037216774821 10000000000000000 16 91 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10223037216774821/10000000000000000 : ℝ)) (X := (14170851018311367889/12500000000000000000 : ℝ)) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(22879921580671/1242900000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(54318804435733/3107250000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (91/16 : ℝ)) (rho := (12429/20000 : ℝ)) (alpha := (22879921580671/1242900000000000 : ℝ)) (beta := (54318804435733/3107250000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (12429/20000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(22879921580671/1242900000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(54318804435733/3107250000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (57197/100000 : ℝ) ^ (91/16 : ℝ) ≤ (4169273278876340557/100000000000000000000 : ℝ) := by
    have hpowers : (57197/100000 : ℝ)^91 ≤ (4169273278876340557/100000000000000000000 : ℝ)^16 := by
      have hnat : (57197 : ℕ)^91*100000000000000000000^16 ≤ 4169273278876340557^16*100000^91 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        57197 100000 4169273278876340557 100000000000000000000 91 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (57197/100000 : ℝ)) (X := (4169273278876340557/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (104169273278876340557/100000000000000000000 : ℝ) ≤ (5036038724326011/5000000000000000 : ℝ) ^ (91/16 : ℝ) := by
    have hpowers : (104169273278876340557/100000000000000000000 : ℝ)^16 ≤ (5036038724326011/5000000000000000 : ℝ)^91 := by
      have hnat : (104169273278876340557 : ℕ)^16*5000000000000000^91 ≤ 5036038724326011^91*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        104169273278876340557 100000000000000000000 5036038724326011 5000000000000000 16 91 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5036038724326011/5000000000000000 : ℝ)) (X := (104169273278876340557/100000000000000000000 : ℝ)) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (54169273278876340557/50000000000000000000 : ℝ) ≤ (5070907604932949/5000000000000000 : ℝ) ^ (91/16 : ℝ) := by
    have hpowers : (54169273278876340557/50000000000000000000 : ℝ)^16 ≤ (5070907604932949/5000000000000000 : ℝ)^91 := by
      have hnat : (54169273278876340557 : ℕ)^16*5000000000000000^91 ≤ 5070907604932949^91*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        54169273278876340557 50000000000000000000 5070907604932949 5000000000000000 16 91 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5070907604932949/5000000000000000 : ℝ)) (X := (54169273278876340557/50000000000000000000 : ℝ)) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(36038724326011/2859850000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(2490634329067/204275000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (91/16 : ℝ)) (rho := (57197/100000 : ℝ)) (alpha := (36038724326011/2859850000000000 : ℝ)) (beta := (2490634329067/204275000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (57197/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(36038724326011/2859850000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(2490634329067/204275000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-438256153/2500000000 : ℝ)*X 0 0+(4372137497/10000000000 : ℝ)*X 0 1+(1431040843/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c328061_s1_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((4604644923/10000000000 : ℝ)*X 1 0+(-351034313/2000000000 : ℝ)*X 1 1+(1375130363/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c328061_s1_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((4642258319/10000000000 : ℝ)*X 2 0+(1529262923/2500000000 : ℝ)*X 2 1+(-863158457/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c328061_s1_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((6545444841/10000000000 : ℝ)*X 0 0+(2376632153/10000000000 : ℝ)*X 0 1+(725240363/2500000000 : ℝ)*X 0 2+(6545444841/10000000000 : ℝ)*X 1 0+(2376632153/10000000000 : ℝ)*X 1 1+(725240363/2500000000 : ℝ)*X 1 2+(6545444841/10000000000 : ℝ)*X 2 0+(2376632153/10000000000 : ℝ)*X 2 1+(725240363/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c328061_s1_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-895667799/5000000000 : ℝ)*X 0 0+(4057358511/10000000000 : ℝ)*X 0 1+(5988254651/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c328061_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((273315231/625000000 : ℝ)*X 1 0+(-1400735563/10000000000 : ℝ)*X 1 1+(2995714917/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c328061_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((1102692939/2500000000 : ℝ)*X 2 0+(6622497363/10000000000 : ℝ)*X 2 1+(-98054899/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c328061_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((6655007061/10000000000 : ℝ)*X 0 0+(762967921/2500000000 : ℝ)*X 0 1+(2079025033/10000000000 : ℝ)*X 0 2+(6655007061/10000000000 : ℝ)*X 1 0+(762967921/2500000000 : ℝ)*X 1 1+(2079025033/10000000000 : ℝ)*X 1 2+(6655007061/10000000000 : ℝ)*X 2 0+(762967921/2500000000 : ℝ)*X 2 1+(2079025033/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c328061_s1_s1_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((-541843829/5000000000 : ℝ)*X 0 0+(1154913641/2500000000 : ℝ)*X 0 1+(1496907769/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c328061_s1_s1_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((1080626369/2500000000 : ℝ)*X 1 0+(-36630549/250000000 : ℝ)*X 1 1+(2995403643/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c328061_s1_s1_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_16 : ((666458493/1250000000 : ℝ)*X 2 0+(5745897091/10000000000 : ℝ)*X 2 1+(-24552741/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c328061_s1_s1_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((1883978913/2500000000 : ℝ)*X 0 0+(977344161/5000000000 : ℝ)*X 0 1+(2081106767/10000000000 : ℝ)*X 0 2+(1883978913/2500000000 : ℝ)*X 1 0+(977344161/5000000000 : ℝ)*X 1 1+(2081106767/10000000000 : ℝ)*X 1 2+(1883978913/2500000000 : ℝ)*X 2 0+(977344161/5000000000 : ℝ)*X 2 1+(2081106767/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c328061_s1_s1_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((-1086136293/10000000000 : ℝ)*X 0 0+(487135853/1000000000 : ℝ)*X 0 1+(5745053623/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c328061_s1_s1_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_22 : ((2645744591/5000000000 : ℝ)*X 1 0+(-543276977/5000000000 : ℝ)*X 1 1+(5332082337/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c328061_s1_s1_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_23 : ((4278918819/10000000000 : ℝ)*X 2 0+(1629463421/2500000000 : ℝ)*X 2 1+(-767018067/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c328061_s1_s1_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_27 : ((7807467911/10000000000 : ℝ)*X 0 0+(346435827/2000000000 : ℝ)*X 0 1+(485237171/2500000000 : ℝ)*X 0 2+(7807467911/10000000000 : ℝ)*X 1 0+(346435827/2000000000 : ℝ)*X 1 1+(485237171/2500000000 : ℝ)*X 1 2+(7807467911/10000000000 : ℝ)*X 2 0+(346435827/2000000000 : ℝ)*X 2 1+(485237171/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c328061_s1_s1_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((11641/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(11641/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (20854791247414402333350691620181/1235171631573250000000000000000000000 : ℝ) := by norm_num
    linear_combination (702877/1000000000000 : ℝ)*(base50) + (789767627809/500000000000 : ℝ)*(base59) + (7093381878461/1000000000000 : ℝ)*(major_s1_0) + (7093381878461/1000000000000 : ℝ)*(major_s1_1) + (7093381878461/1000000000000 : ℝ)*(major_s1_2) + (4804383/40000000000 : ℝ)*(sp_s1_0) + (38190369/1000000000000 : ℝ)*(sp_s1_1) + (3415197/50000000000 : ℝ)*(sp_s1_6) + (10917421806161/1000000000000 : ℝ)*(sp_s1_7) + (1091657685771/100000000000 : ℝ)*(sp_s1_8) + (218347169921/20000000000 : ℝ)*(sp_s1_9) + (8172869773/2500000000 : ℝ)*(sp_s1_13) + (926867657/1000000000000 : ℝ)*(sp_s1_15) + (91709843/500000000000 : ℝ)*(sp_s1_23) + (163460810657/50000000000 : ℝ)*(f.failure) + (1364692739467/125000000000 : ℝ)*(f.sum) + (8074114490337841013/14218030260000000000000000000000 : ℝ)*base63 + (15868680621551/102137500000000000000000000 : ℝ)*base64 + (644163496000781/1553625000000000000000000000 : ℝ)*base66 + (66515370080839/714962500000000000000000000 : ℝ)*base69 + (447405090173200451/6388598487500000000000000000000 : ℝ)*base70 + (111586748308731/6254900000000000000000000000 : ℝ)*base72 + (607289744332871/1242900000000000000000000000 : ℝ)*base75 + (59371644050023/3127450000000000000000000000 : ℝ)*base76 + (134301586001259793921/388710760500000000000000000000000 : ℝ)*base78 + (97/200000000000000 : ℝ)*base86 + (97/200000000000000 : ℝ)*base88 + (97/200000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(29769/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(29769/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (10633962337861520994377338485583/1235171631573250000000000000000000000 : ℝ) := by norm_num
    linear_combination (1380583/1000000000000 : ℝ)*(base13) + (59438967507/62500000000 : ℝ)*(base59) + (6688299601443/1000000000000 : ℝ)*(major_s1_0) + (6688299601443/1000000000000 : ℝ)*(major_s1_1) + (6688299601443/1000000000000 : ℝ)*(major_s1_2) + (7181581/500000000000 : ℝ)*(sp_s1_2) + (57814351/1000000000000 : ℝ)*(sp_s1_6) + (13348553/500000000000 : ℝ)*(sp_s1_7) + (5781247/100000000000 : ℝ)*(sp_s1_8) + (2058809482269/200000000000 : ℝ)*(sp_s1_14) + (2573504419141/250000000000 : ℝ)*(sp_s1_15) + (643378820367/62500000000 : ℝ)*(sp_s1_16) + (616441586371/200000000000 : ℝ)*(sp_s1_20) + (2040783/8000000000 : ℝ)*(sp_s1_27) + (38531510551/12500000000 : ℝ)*(f.failure) + (5147037744517/500000000000 : ℝ)*(f.sum) + (3014766543965731151/4739343420000000000000000000000 : ℝ)*base62 + (7032587998409/204275000000000000000000000 : ℝ)*base65 + (12884323718447/64734375000000000000000000 : ℝ)*base66 + (1444252755670727/2859850000000000000000000000 : ℝ)*base68 + (4995365379541066787/25554393950000000000000000000000 : ℝ)*base70 + (550198026800043/6254900000000000000000000000 : ℝ)*base72 + (214655046106709/414300000000000000000000000 : ℝ)*base74 + (168773793468789/3127450000000000000000000000 : ℝ)*base76 + (28036172276169571091/129570253500000000000000000000000 : ℝ)*base78 + (21/50000000000000 : ℝ)*base86 + (21/50000000000000 : ℝ)*base88 + (21/50000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(27093/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(27093/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (2823763243801518006286484165423/247034326314650000000000000000000000 : ℝ) := by norm_num
    linear_combination (3388233/250000000000 : ℝ)*(base11) + (1671099/250000000000 : ℝ)*(base15) + (99053214321/250000000000 : ℝ)*(base40) + (978725361453/1000000000000 : ℝ)*(base59) + (309303569697/50000000000 : ℝ)*(major_s1_0) + (309303569697/50000000000 : ℝ)*(major_s1_1) + (309303569697/50000000000 : ℝ)*(major_s1_2) + (1709269/100000000000 : ℝ)*(sp_s1_0) + (3229161/100000000000 : ℝ)*(sp_s1_2) + (57761859/1000000000000 : ℝ)*(sp_s1_9) + (9521055725083/1000000000000 : ℝ)*(sp_s1_21) + (2380269921577/250000000000 : ℝ)*(sp_s1_22) + (1904199263447/200000000000 : ℝ)*(sp_s1_23) + (570210521391/200000000000 : ℝ)*(sp_s1_27) + (570210521391/200000000000 : ℝ)*(f.failure) + (595067898169/62500000000 : ℝ)*(f.sum) + (1256592165981169/592417927500000000000000000000 : ℝ)*base62 + (40104211214087/81710000000000000000000000 : ℝ)*base64 + (140150645266567/207150000000000000000000000 : ℝ)*base66 + (121555694411349/571970000000000000000000000 : ℝ)*base68 + (880921756250231521/5110878790000000000000000000000 : ℝ)*base71 + (70078011284079/312745000000000000000000000 : ℝ)*base72 + (6141310484947/20715000000000000000000000 : ℝ)*base74 + (49027157410871/312745000000000000000000000 : ℝ)*base76 + (729434734971661313/12957025350000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base81 + (489/800000000000000 : ℝ)*base87 + (489/800000000000000 : ℝ)*base89 + (489/800000000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (8679/4000 : ℝ) (80697/50000 : ℝ) (82433/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]])
    (hprev0 : (0 : ℝ) ≤ ((62549/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(62549/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(12429/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(12429/20000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(57197/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(57197/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((11641/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(11641/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(29769/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(29769/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(27093/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(27093/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c328061_s1 p hpa hpb X hX hprev0

#print axioms solution
