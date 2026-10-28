-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c301058_s3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:35:09.150805+00:00
-- url     : https://prove2.me/submissions/07a88504-9f61-47a3-93fa-f8c015624f2c

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
theorem collision_support_c301058_s3_s3_0 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-452776867/1250000000 : ℝ)*x 0 + (3501064587/10000000000 : ℝ)*x 1 + (-292693809/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (452776867/1250000000 : ℝ)^65 ≤ (25999548014249/100000000000000 : ℝ)^49 := by
    have hnat : (452776867 : ℕ)^65*100000000000000^49 ≤ 25999548014249^49*1250000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      452776867 1250000000 25999548014249 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3501064587/10000000000 : ℝ)^65 ≤ (388318012003/1562500000000 : ℝ)^49 := by
    have hnat : (3501064587 : ℕ)^65*1562500000000^49 ≤ 388318012003^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3501064587 10000000000 388318012003 1562500000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (292693809/500000000 : ℝ)^65 ≤ (49148099206657/100000000000000 : ℝ)^49 := by
    have hnat : (292693809 : ℕ)^65*100000000000000^49 ≤ 49148099206657^49*500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      292693809 500000000 49148099206657 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-452776867/1250000000 : ℝ), (3501064587/10000000000 : ℝ), (-292693809/500000000 : ℝ)] ![(25999548014249/100000000000000 : ℝ), (388318012003/1562500000000 : ℝ), (49148099206657/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-452776867/1250000000 : ℝ)|^65 ≤ (25999548014249/100000000000000 : ℝ)^49
        have hw : |(-452776867/1250000000 : ℝ)|=(452776867/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3501064587/10000000000 : ℝ)|^65 ≤ (388318012003/1562500000000 : ℝ)^49
        have hw : |(3501064587/10000000000 : ℝ)|=(3501064587/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-292693809/500000000 : ℝ)|^65 ≤ (49148099206657/100000000000000 : ℝ)^49
        have hw : |(-292693809/500000000 : ℝ)|=(292693809/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301058_s3_s3_1 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3272907507/10000000000 : ℝ)*x 0 + (-393890379/1250000000 : ℝ)*x 1 + (-1285916061/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3272907507/10000000000 : ℝ)^65 ≤ (22727137886661/100000000000000 : ℝ)^49 := by
    have hnat : (3272907507 : ℕ)^65*100000000000000^49 ≤ 22727137886661^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3272907507 10000000000 22727137886661 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (393890379/1250000000 : ℝ)^65 ≤ (10806099231819/50000000000000 : ℝ)^49 := by
    have hnat : (393890379 : ℕ)^65*50000000000000^49 ≤ 10806099231819^49*1250000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      393890379 1250000000 10806099231819 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1285916061/2000000000 : ℝ)^65 ≤ (27830331819521/50000000000000 : ℝ)^49 := by
    have hnat : (1285916061 : ℕ)^65*50000000000000^49 ≤ 27830331819521^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1285916061 2000000000 27830331819521 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3272907507/10000000000 : ℝ), (-393890379/1250000000 : ℝ), (-1285916061/2000000000 : ℝ)] ![(22727137886661/100000000000000 : ℝ), (10806099231819/50000000000000 : ℝ), (27830331819521/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3272907507/10000000000 : ℝ)|^65 ≤ (22727137886661/100000000000000 : ℝ)^49
        have hw : |(3272907507/10000000000 : ℝ)|=(3272907507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-393890379/1250000000 : ℝ)|^65 ≤ (10806099231819/50000000000000 : ℝ)^49
        have hw : |(-393890379/1250000000 : ℝ)|=(393890379/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1285916061/2000000000 : ℝ)|^65 ≤ (27830331819521/50000000000000 : ℝ)^49
        have hw : |(-1285916061/2000000000 : ℝ)|=(1285916061/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301058_s3_s3_2 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5536709699/10000000000 : ℝ)*x 0 + (1072657719/2000000000 : ℝ)*x 1 + (460180627/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5536709699/10000000000 : ℝ)^65 ≤ (1141183804529/2500000000000 : ℝ)^49 := by
    have hnat : (5536709699 : ℕ)^65*2500000000000^49 ≤ 1141183804529^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5536709699 10000000000 1141183804529 2500000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1072657719/2000000000 : ℝ)^65 ≤ (21880244174237/50000000000000 : ℝ)^49 := by
    have hnat : (1072657719 : ℕ)^65*50000000000000^49 ≤ 21880244174237^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1072657719 2000000000 21880244174237 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (460180627/2500000000 : ℝ)^65 ≤ (10592159450633/100000000000000 : ℝ)^49 := by
    have hnat : (460180627 : ℕ)^65*100000000000000^49 ≤ 10592159450633^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      460180627 2500000000 10592159450633 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5536709699/10000000000 : ℝ), (1072657719/2000000000 : ℝ), (460180627/2500000000 : ℝ)] ![(1141183804529/2500000000000 : ℝ), (21880244174237/50000000000000 : ℝ), (10592159450633/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5536709699/10000000000 : ℝ)|^65 ≤ (1141183804529/2500000000000 : ℝ)^49
        have hw : |(5536709699/10000000000 : ℝ)|=(5536709699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1072657719/2000000000 : ℝ)|^65 ≤ (21880244174237/50000000000000 : ℝ)^49
        have hw : |(1072657719/2000000000 : ℝ)|=(1072657719/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(460180627/2500000000 : ℝ)|^65 ≤ (10592159450633/100000000000000 : ℝ)^49
        have hw : |(460180627/2500000000 : ℝ)|=(460180627/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301058_s3_s3_7 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-3099336317/10000000000 : ℝ)*x 0 + (10988601/40000000 : ℝ)*x 1 + (-1718939313/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3099336317/10000000000 : ℝ)^65 ≤ (2114230647839/10000000000000 : ℝ)^49 := by
    have hnat : (3099336317 : ℕ)^65*10000000000000^49 ≤ 2114230647839^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3099336317 10000000000 2114230647839 10000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (10988601/40000000 : ℝ)^65 ≤ (4504020436267/25000000000000 : ℝ)^49 := by
    have hnat : (10988601 : ℕ)^65*25000000000000^49 ≤ 4504020436267^49*40000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10988601 40000000 4504020436267 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1718939313/2500000000 : ℝ)^65 ≤ (60841611755831/100000000000000 : ℝ)^49 := by
    have hnat : (1718939313 : ℕ)^65*100000000000000^49 ≤ 60841611755831^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1718939313 2500000000 60841611755831 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3099336317/10000000000 : ℝ), (10988601/40000000 : ℝ), (-1718939313/2500000000 : ℝ)] ![(2114230647839/10000000000000 : ℝ), (4504020436267/25000000000000 : ℝ), (60841611755831/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3099336317/10000000000 : ℝ)|^65 ≤ (2114230647839/10000000000000 : ℝ)^49
        have hw : |(-3099336317/10000000000 : ℝ)|=(3099336317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(10988601/40000000 : ℝ)|^65 ≤ (4504020436267/25000000000000 : ℝ)^49
        have hw : |(10988601/40000000 : ℝ)|=(10988601/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1718939313/2500000000 : ℝ)|^65 ≤ (60841611755831/100000000000000 : ℝ)^49
        have hw : |(-1718939313/2500000000 : ℝ)|=(1718939313/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301058_s3_s3_8 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3258869161/10000000000 : ℝ)*x 0 + (-6976561/25000000 : ℝ)*x 1 + (-6718859237/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3258869161/10000000000 : ℝ)^65 ≤ (22597914921417/100000000000000 : ℝ)^49 := by
    have hnat : (3258869161 : ℕ)^65*100000000000000^49 ≤ 22597914921417^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3258869161 10000000000 22597914921417 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6976561/25000000 : ℝ)^65 ≤ (18395259628313/100000000000000 : ℝ)^49 := by
    have hnat : (6976561 : ℕ)^65*100000000000000^49 ≤ 18395259628313^49*25000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6976561 25000000 18395259628313 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6718859237/10000000000 : ℝ)^65 ≤ (29503412721031/50000000000000 : ℝ)^49 := by
    have hnat : (6718859237 : ℕ)^65*50000000000000^49 ≤ 29503412721031^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6718859237 10000000000 29503412721031 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3258869161/10000000000 : ℝ), (-6976561/25000000 : ℝ), (-6718859237/10000000000 : ℝ)] ![(22597914921417/100000000000000 : ℝ), (18395259628313/100000000000000 : ℝ), (29503412721031/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3258869161/10000000000 : ℝ)|^65 ≤ (22597914921417/100000000000000 : ℝ)^49
        have hw : |(3258869161/10000000000 : ℝ)|=(3258869161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-6976561/25000000 : ℝ)|^65 ≤ (18395259628313/100000000000000 : ℝ)^49
        have hw : |(-6976561/25000000 : ℝ)|=(6976561/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6718859237/10000000000 : ℝ)|^65 ≤ (29503412721031/50000000000000 : ℝ)^49
        have hw : |(-6718859237/10000000000 : ℝ)|=(6718859237/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301058_s3_s3_9 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5513195389/10000000000 : ℝ)*x 0 + (2856031093/5000000000 : ℝ)*x 1 + (1352071517/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5513195389/10000000000 : ℝ)^65 ≤ (5673795597813/12500000000000 : ℝ)^49 := by
    have hnat : (5513195389 : ℕ)^65*12500000000000^49 ≤ 5673795597813^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5513195389 10000000000 5673795597813 12500000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2856031093/5000000000 : ℝ)^65 ≤ (47574953488427/100000000000000 : ℝ)^49 := by
    have hnat : (2856031093 : ℕ)^65*100000000000000^49 ≤ 47574953488427^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2856031093 5000000000 47574953488427 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1352071517/10000000000 : ℝ)^65 ≤ (3517340854871/50000000000000 : ℝ)^49 := by
    have hnat : (1352071517 : ℕ)^65*50000000000000^49 ≤ 3517340854871^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1352071517 10000000000 3517340854871 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5513195389/10000000000 : ℝ), (2856031093/5000000000 : ℝ), (1352071517/10000000000 : ℝ)] ![(5673795597813/12500000000000 : ℝ), (47574953488427/100000000000000 : ℝ), (3517340854871/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5513195389/10000000000 : ℝ)|^65 ≤ (5673795597813/12500000000000 : ℝ)^49
        have hw : |(5513195389/10000000000 : ℝ)|=(5513195389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2856031093/5000000000 : ℝ)|^65 ≤ (47574953488427/100000000000000 : ℝ)^49
        have hw : |(2856031093/5000000000 : ℝ)|=(2856031093/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1352071517/10000000000 : ℝ)|^65 ≤ (3517340854871/50000000000000 : ℝ)^49
        have hw : |(1352071517/10000000000 : ℝ)|=(1352071517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301058_s3_s3_13 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4030467401/10000000000 : ℝ)*x 0 + (7565721461/10000000000 : ℝ)*x 1 + (-304367771/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4030467401/10000000000 : ℝ)^65 ≤ (29956555422287/100000000000000 : ℝ)^49 := by
    have hnat : (4030467401 : ℕ)^65*100000000000000^49 ≤ 29956555422287^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4030467401 10000000000 29956555422287 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7565721461/10000000000 : ℝ)^65 ≤ (69070289826477/100000000000000 : ℝ)^49 := by
    have hnat : (7565721461 : ℕ)^65*100000000000000^49 ≤ 69070289826477^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7565721461 10000000000 69070289826477 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (304367771/10000000000 : ℝ)^65 ≤ (973154736957/100000000000000 : ℝ)^49 := by
    have hnat : (304367771 : ℕ)^65*100000000000000^49 ≤ 973154736957^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      304367771 10000000000 973154736957 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4030467401/10000000000 : ℝ), (7565721461/10000000000 : ℝ), (-304367771/10000000000 : ℝ)] ![(29956555422287/100000000000000 : ℝ), (69070289826477/100000000000000 : ℝ), (973154736957/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4030467401/10000000000 : ℝ)|^65 ≤ (29956555422287/100000000000000 : ℝ)^49
        have hw : |(4030467401/10000000000 : ℝ)|=(4030467401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7565721461/10000000000 : ℝ)|^65 ≤ (69070289826477/100000000000000 : ℝ)^49
        have hw : |(7565721461/10000000000 : ℝ)|=(7565721461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-304367771/10000000000 : ℝ)|^65 ≤ (973154736957/100000000000000 : ℝ)^49
        have hw : |(-304367771/10000000000 : ℝ)|=(304367771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301058_s3_s3_14 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-284072307/1000000000 : ℝ)*x 0 + (1537610261/5000000000 : ℝ)*x 1 + (-6824529357/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (284072307/1000000000 : ℝ)^65 ≤ (18834613031197/100000000000000 : ℝ)^49 := by
    have hnat : (284072307 : ℕ)^65*100000000000000^49 ≤ 18834613031197^49*1000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      284072307 1000000000 18834613031197 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1537610261/5000000000 : ℝ)^65 ≤ (20924360183801/100000000000000 : ℝ)^49 := by
    have hnat : (1537610261 : ℕ)^65*100000000000000^49 ≤ 20924360183801^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1537610261 5000000000 20924360183801 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6824529357/10000000000 : ℝ)^65 ≤ (60241026766959/100000000000000 : ℝ)^49 := by
    have hnat : (6824529357 : ℕ)^65*100000000000000^49 ≤ 60241026766959^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6824529357 10000000000 60241026766959 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-284072307/1000000000 : ℝ), (1537610261/5000000000 : ℝ), (-6824529357/10000000000 : ℝ)] ![(18834613031197/100000000000000 : ℝ), (20924360183801/100000000000000 : ℝ), (60241026766959/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-284072307/1000000000 : ℝ)|^65 ≤ (18834613031197/100000000000000 : ℝ)^49
        have hw : |(-284072307/1000000000 : ℝ)|=(284072307/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1537610261/5000000000 : ℝ)|^65 ≤ (20924360183801/100000000000000 : ℝ)^49
        have hw : |(1537610261/5000000000 : ℝ)|=(1537610261/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6824529357/10000000000 : ℝ)|^65 ≤ (60241026766959/100000000000000 : ℝ)^49
        have hw : |(-6824529357/10000000000 : ℝ)|=(6824529357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301058_s3_s3_15 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (284072307/1000000000 : ℝ)*x 0 + (-1537610261/5000000000 : ℝ)*x 1 + (-6824529357/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (284072307/1000000000 : ℝ)^65 ≤ (18834613031197/100000000000000 : ℝ)^49 := by
    have hnat : (284072307 : ℕ)^65*100000000000000^49 ≤ 18834613031197^49*1000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      284072307 1000000000 18834613031197 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1537610261/5000000000 : ℝ)^65 ≤ (20924360183801/100000000000000 : ℝ)^49 := by
    have hnat : (1537610261 : ℕ)^65*100000000000000^49 ≤ 20924360183801^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1537610261 5000000000 20924360183801 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6824529357/10000000000 : ℝ)^65 ≤ (60241026766959/100000000000000 : ℝ)^49 := by
    have hnat : (6824529357 : ℕ)^65*100000000000000^49 ≤ 60241026766959^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6824529357 10000000000 60241026766959 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(284072307/1000000000 : ℝ), (-1537610261/5000000000 : ℝ), (-6824529357/10000000000 : ℝ)] ![(18834613031197/100000000000000 : ℝ), (20924360183801/100000000000000 : ℝ), (60241026766959/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(284072307/1000000000 : ℝ)|^65 ≤ (18834613031197/100000000000000 : ℝ)^49
        have hw : |(284072307/1000000000 : ℝ)|=(284072307/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1537610261/5000000000 : ℝ)|^65 ≤ (20924360183801/100000000000000 : ℝ)^49
        have hw : |(-1537610261/5000000000 : ℝ)|=(1537610261/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6824529357/10000000000 : ℝ)|^65 ≤ (60241026766959/100000000000000 : ℝ)^49
        have hw : |(-6824529357/10000000000 : ℝ)|=(6824529357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301058_s3_s3_16 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (623894647/1000000000 : ℝ)*x 0 + (1300509613/2500000000 : ℝ)*x 1 + (241121063/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (623894647/1000000000 : ℝ)^65 ≤ (2674107227737/5000000000000 : ℝ)^49 := by
    have hnat : (623894647 : ℕ)^65*5000000000000^49 ≤ 2674107227737^49*1000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      623894647 1000000000 2674107227737 5000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1300509613/2500000000 : ℝ)^65 ≤ (10505955208091/25000000000000 : ℝ)^49 := by
    have hnat : (1300509613 : ℕ)^65*25000000000000^49 ≤ 10505955208091^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1300509613 2500000000 10505955208091 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (241121063/2500000000 : ℝ)^65 ≤ (4494034596447/100000000000000 : ℝ)^49 := by
    have hnat : (241121063 : ℕ)^65*100000000000000^49 ≤ 4494034596447^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      241121063 2500000000 4494034596447 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(623894647/1000000000 : ℝ), (1300509613/2500000000 : ℝ), (241121063/2500000000 : ℝ)] ![(2674107227737/5000000000000 : ℝ), (10505955208091/25000000000000 : ℝ), (4494034596447/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(623894647/1000000000 : ℝ)|^65 ≤ (2674107227737/5000000000000 : ℝ)^49
        have hw : |(623894647/1000000000 : ℝ)|=(623894647/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1300509613/2500000000 : ℝ)|^65 ≤ (10505955208091/25000000000000 : ℝ)^49
        have hw : |(1300509613/2500000000 : ℝ)|=(1300509613/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(241121063/2500000000 : ℝ)|^65 ≤ (4494034596447/100000000000000 : ℝ)^49
        have hw : |(241121063/2500000000 : ℝ)|=(241121063/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301058_s3_s3_19 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (0 : ℝ)*x 0 + (0 : ℝ)*x 1 + (-1 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (0 : ℝ)^65 ≤ (0 : ℝ)^49 := by
    have hnat : (0 : ℕ)^65*1^49 ≤ 0^49*1^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      0 1 0 1 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (0 : ℝ)^65 ≤ (0 : ℝ)^49 := by
    have hnat : (0 : ℕ)^65*1^49 ≤ 0^49*1^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      0 1 0 1 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1 : ℝ)^65 ≤ (1 : ℝ)^49 := by
    have hnat : (1 : ℕ)^65*1^49 ≤ 1^49*1^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1 1 1 1 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(0 : ℝ), (0 : ℝ), (-1 : ℝ)] ![(0 : ℝ), (0 : ℝ), (1 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(0 : ℝ)|^65 ≤ (0 : ℝ)^49
        have hw : |(0 : ℝ)|=(0 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(0 : ℝ)|^65 ≤ (0 : ℝ)^49
        have hw : |(0 : ℝ)|=(0 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1 : ℝ)|^65 ≤ (1 : ℝ)^49
        have hw : |(-1 : ℝ)|=(1 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301058_s3_s3_20 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (623894647/1000000000 : ℝ)*x 0 + (1300509613/2500000000 : ℝ)*x 1 + (-241121063/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (623894647/1000000000 : ℝ)^65 ≤ (2674107227737/5000000000000 : ℝ)^49 := by
    have hnat : (623894647 : ℕ)^65*5000000000000^49 ≤ 2674107227737^49*1000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      623894647 1000000000 2674107227737 5000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1300509613/2500000000 : ℝ)^65 ≤ (10505955208091/25000000000000 : ℝ)^49 := by
    have hnat : (1300509613 : ℕ)^65*25000000000000^49 ≤ 10505955208091^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1300509613 2500000000 10505955208091 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (241121063/2500000000 : ℝ)^65 ≤ (4494034596447/100000000000000 : ℝ)^49 := by
    have hnat : (241121063 : ℕ)^65*100000000000000^49 ≤ 4494034596447^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      241121063 2500000000 4494034596447 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(623894647/1000000000 : ℝ), (1300509613/2500000000 : ℝ), (-241121063/2500000000 : ℝ)] ![(2674107227737/5000000000000 : ℝ), (10505955208091/25000000000000 : ℝ), (4494034596447/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(623894647/1000000000 : ℝ)|^65 ≤ (2674107227737/5000000000000 : ℝ)^49
        have hw : |(623894647/1000000000 : ℝ)|=(623894647/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1300509613/2500000000 : ℝ)|^65 ≤ (10505955208091/25000000000000 : ℝ)^49
        have hw : |(1300509613/2500000000 : ℝ)|=(1300509613/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-241121063/2500000000 : ℝ)|^65 ≤ (4494034596447/100000000000000 : ℝ)^49
        have hw : |(-241121063/2500000000 : ℝ)|=(241121063/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301058_s3_s3_21 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-3544973567/10000000000 : ℝ)*x 0 + (862195069/2500000000 : ℝ)*x 1 + (-745430581/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3544973567/10000000000 : ℝ)^65 ≤ (1579166331619/6250000000000 : ℝ)^49 := by
    have hnat : (3544973567 : ℕ)^65*6250000000000^49 ≤ 1579166331619^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3544973567 10000000000 1579166331619 6250000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (862195069/2500000000 : ℝ)^65 ≤ (24361227485043/100000000000000 : ℝ)^49 := by
    have hnat : (862195069 : ℕ)^65*100000000000000^49 ≤ 24361227485043^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      862195069 2500000000 24361227485043 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (745430581/1250000000 : ℝ)^65 ≤ (5037211119323/10000000000000 : ℝ)^49 := by
    have hnat : (745430581 : ℕ)^65*10000000000000^49 ≤ 5037211119323^49*1250000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      745430581 1250000000 5037211119323 10000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3544973567/10000000000 : ℝ), (862195069/2500000000 : ℝ), (-745430581/1250000000 : ℝ)] ![(1579166331619/6250000000000 : ℝ), (24361227485043/100000000000000 : ℝ), (5037211119323/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3544973567/10000000000 : ℝ)|^65 ≤ (1579166331619/6250000000000 : ℝ)^49
        have hw : |(-3544973567/10000000000 : ℝ)|=(3544973567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(862195069/2500000000 : ℝ)|^65 ≤ (24361227485043/100000000000000 : ℝ)^49
        have hw : |(862195069/2500000000 : ℝ)|=(862195069/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-745430581/1250000000 : ℝ)|^65 ≤ (5037211119323/10000000000000 : ℝ)^49
        have hw : |(-745430581/1250000000 : ℝ)|=(745430581/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301058_s3_s3_22 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1699398727/5000000000 : ℝ)*x 0 + (-650068047/2000000000 : ℝ)*x 1 + (-6248122761/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1699398727/5000000000 : ℝ)^65 ≤ (2986748507801/12500000000000 : ℝ)^49 := by
    have hnat : (1699398727 : ℕ)^65*12500000000000^49 ≤ 2986748507801^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1699398727 5000000000 2986748507801 12500000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (650068047/2000000000 : ℝ)^65 ≤ (11259747414503/50000000000000 : ℝ)^49 := by
    have hnat : (650068047 : ℕ)^65*50000000000000^49 ≤ 11259747414503^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      650068047 2000000000 11259747414503 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6248122761/10000000000 : ℝ)^65 ≤ (53586517093951/100000000000000 : ℝ)^49 := by
    have hnat : (6248122761 : ℕ)^65*100000000000000^49 ≤ 53586517093951^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6248122761 10000000000 53586517093951 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1699398727/5000000000 : ℝ), (-650068047/2000000000 : ℝ), (-6248122761/10000000000 : ℝ)] ![(2986748507801/12500000000000 : ℝ), (11259747414503/50000000000000 : ℝ), (53586517093951/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1699398727/5000000000 : ℝ)|^65 ≤ (2986748507801/12500000000000 : ℝ)^49
        have hw : |(1699398727/5000000000 : ℝ)|=(1699398727/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-650068047/2000000000 : ℝ)|^65 ≤ (11259747414503/50000000000000 : ℝ)^49
        have hw : |(-650068047/2000000000 : ℝ)|=(650068047/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6248122761/10000000000 : ℝ)|^65 ≤ (53586517093951/100000000000000 : ℝ)^49
        have hw : |(-6248122761/10000000000 : ℝ)|=(6248122761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301058_s3_s3_23 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1315014161/2000000000 : ℝ)*x 0 + (842267229/2000000000 : ℝ)*x 1 + (941082411/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1315014161/2000000000 : ℝ)^65 ≤ (11467515791537/20000000000000 : ℝ)^49 := by
    have hnat : (1315014161 : ℕ)^65*20000000000000^49 ≤ 11467515791537^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1315014161 2000000000 11467515791537 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (842267229/2000000000 : ℝ)^65 ≤ (6350552431461/20000000000000 : ℝ)^49 := by
    have hnat : (842267229 : ℕ)^65*20000000000000^49 ≤ 6350552431461^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      842267229 2000000000 6350552431461 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (941082411/5000000000 : ℝ)^65 ≤ (68185367963/625000000000 : ℝ)^49 := by
    have hnat : (941082411 : ℕ)^65*625000000000^49 ≤ 68185367963^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      941082411 5000000000 68185367963 625000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1315014161/2000000000 : ℝ), (842267229/2000000000 : ℝ), (941082411/5000000000 : ℝ)] ![(11467515791537/20000000000000 : ℝ), (6350552431461/20000000000000 : ℝ), (68185367963/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1315014161/2000000000 : ℝ)|^65 ≤ (11467515791537/20000000000000 : ℝ)^49
        have hw : |(1315014161/2000000000 : ℝ)|=(1315014161/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(842267229/2000000000 : ℝ)|^65 ≤ (6350552431461/20000000000000 : ℝ)^49
        have hw : |(842267229/2000000000 : ℝ)|=(842267229/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(941082411/5000000000 : ℝ)|^65 ≤ (68185367963/625000000000 : ℝ)^49
        have hw : |(941082411/5000000000 : ℝ)|=(941082411/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301058_s3_s3_27 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (155421003/500000000 : ℝ)*x 0 + (8216889053/10000000000 : ℝ)*x 1 + (-465641381/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (155421003/500000000 : ℝ)^65 ≤ (21224544641559/100000000000000 : ℝ)^49 := by
    have hnat : (155421003 : ℕ)^65*100000000000000^49 ≤ 21224544641559^49*500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      155421003 500000000 21224544641559 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8216889053/10000000000 : ℝ)^65 ≤ (38532464768571/50000000000000 : ℝ)^49 := by
    have hnat : (8216889053 : ℕ)^65*50000000000000^49 ≤ 38532464768571^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8216889053 10000000000 38532464768571 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (465641381/10000000000 : ℝ)^65 ≤ (1710525810793/100000000000000 : ℝ)^49 := by
    have hnat : (465641381 : ℕ)^65*100000000000000^49 ≤ 1710525810793^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      465641381 10000000000 1710525810793 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(155421003/500000000 : ℝ), (8216889053/10000000000 : ℝ), (-465641381/10000000000 : ℝ)] ![(21224544641559/100000000000000 : ℝ), (38532464768571/50000000000000 : ℝ), (1710525810793/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(155421003/500000000 : ℝ)|^65 ≤ (21224544641559/100000000000000 : ℝ)^49
        have hw : |(155421003/500000000 : ℝ)|=(155421003/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(8216889053/10000000000 : ℝ)|^65 ≤ (38532464768571/50000000000000 : ℝ)^49
        have hw : |(8216889053/10000000000 : ℝ)|=(8216889053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-465641381/10000000000 : ℝ)|^65 ≤ (1710525810793/100000000000000 : ℝ)^49
        have hw : |(-465641381/10000000000 : ℝ)|=(465641381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c301058_s3 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (36981/25000 : ℝ) (92391/50000 : ℝ) (4759/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, false]])
    (hprev2 : (0 : ℝ) ≤ ((80737/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(80737/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(71027/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(71027/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-29459/50000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(-29459/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((25211/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(25211/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(21733/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(21733/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-19721/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(-19721/100000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (4759/6250 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (4759/6250 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (4759/6250 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (4759/6250 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (4759/6250 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (4759/6250 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
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
  rcases hprev2 with ⟨ratio_s2_0,ratio_s2_1,ratio_s2_2⟩
  have s3_pow0 : (80737/100000 : ℝ) ^ (129/32 : ℝ) ≤ (42207191127764368311/100000000000000000000 : ℝ) := by
    have hpowers : (80737/100000 : ℝ)^129 ≤ (42207191127764368311/100000000000000000000 : ℝ)^32 := by
      have hnat : (80737 : ℕ)^129*100000000000000000000^32 ≤ 42207191127764368311^32*100000^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        80737 100000 42207191127764368311 100000000000000000000 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (80737/100000 : ℝ)) (X := (42207191127764368311/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s3_corner0a : (142207191127764368311/100000000000000000000 : ℝ) ≤ (5456372787551289/5000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (142207191127764368311/100000000000000000000 : ℝ)^32 ≤ (5456372787551289/5000000000000000 : ℝ)^129 := by
      have hnat : (142207191127764368311 : ℕ)^32*5000000000000000^129 ≤ 5456372787551289^129*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        142207191127764368311 100000000000000000000 5456372787551289 5000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5456372787551289/5000000000000000 : ℝ)) (X := (142207191127764368311/100000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s3_corner0b : (92207191127764368311/50000000000000000000 : ℝ) ≤ (5819740166810373/5000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (92207191127764368311/50000000000000000000 : ℝ)^32 ≤ (5819740166810373/5000000000000000 : ℝ)^129 := by
      have hnat : (92207191127764368311 : ℕ)^32*5000000000000000^129 ≤ 5819740166810373^129*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        92207191127764368311 50000000000000000000 5819740166810373 5000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5819740166810373/5000000000000000 : ℝ)) (X := (92207191127764368311/50000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s3_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(456372787551289/4036850000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(90841844814771/1009212500000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (80737/100000 : ℝ)) (alpha := (456372787551289/4036850000000000 : ℝ)) (beta := (90841844814771/1009212500000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow0,s3_corner0a]) (by linarith only [s3_pow0,s3_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (80737/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(456372787551289/4036850000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(90841844814771/1009212500000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s3_pow1 : (71027/100000 : ℝ) ^ (129/32 : ℝ) ≤ (25179718453406695851/100000000000000000000 : ℝ) := by
    have hpowers : (71027/100000 : ℝ)^129 ≤ (25179718453406695851/100000000000000000000 : ℝ)^32 := by
      have hnat : (71027 : ℕ)^129*100000000000000000000^32 ≤ 25179718453406695851^32*100000^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        71027 100000 25179718453406695851 100000000000000000000 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (71027/100000 : ℝ)) (X := (25179718453406695851/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s3_corner1a : (125179718453406695851/100000000000000000000 : ℝ) ≤ (5286454244283793/5000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (125179718453406695851/100000000000000000000 : ℝ)^32 ≤ (5286454244283793/5000000000000000 : ℝ)^129 := by
      have hnat : (125179718453406695851 : ℕ)^32*5000000000000000^129 ≤ 5286454244283793^129*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        125179718453406695851 100000000000000000000 5286454244283793 5000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5286454244283793/5000000000000000 : ℝ)) (X := (125179718453406695851/100000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s3_corner1b : (75179718453406695851/50000000000000000000 : ℝ) ≤ (5532346851447797/5000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (75179718453406695851/50000000000000000000 : ℝ)^32 ≤ (5532346851447797/5000000000000000 : ℝ)^129 := by
      have hnat : (75179718453406695851 : ℕ)^32*5000000000000000^129 ≤ 5532346851447797^129*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        75179718453406695851 50000000000000000000 5532346851447797 5000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5532346851447797/5000000000000000 : ℝ)) (X := (75179718453406695851/50000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s3_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(286454244283793/3551350000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(61473151791001/887837500000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (71027/100000 : ℝ)) (alpha := (286454244283793/3551350000000000 : ℝ)) (beta := (61473151791001/887837500000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow1,s3_corner1a]) (by linarith only [s3_pow1,s3_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (71027/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(286454244283793/3551350000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(61473151791001/887837500000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s3_pow2 : (29459/50000 : ℝ) ^ (129/32 : ℝ) ≤ (11852561957760130711/100000000000000000000 : ℝ) := by
    have hpowers : (29459/50000 : ℝ)^129 ≤ (11852561957760130711/100000000000000000000 : ℝ)^32 := by
      have hnat : (29459 : ℕ)^129*100000000000000000000^32 ≤ 11852561957760130711^32*50000^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        29459 50000 11852561957760130711 100000000000000000000 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (29459/50000 : ℝ)) (X := (11852561957760130711/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s3_corner2a : (111852561957760130711/100000000000000000000 : ℝ) ≤ (5140877001693983/5000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (111852561957760130711/100000000000000000000 : ℝ)^32 ≤ (5140877001693983/5000000000000000 : ℝ)^129 := by
      have hnat : (111852561957760130711 : ℕ)^32*5000000000000000^129 ≤ 5140877001693983^129*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        111852561957760130711 100000000000000000000 5140877001693983 5000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5140877001693983/5000000000000000 : ℝ)) (X := (111852561957760130711/100000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s3_corner2b : (61852561957760130711/50000000000000000000 : ℝ) ≤ (10541875339356501/10000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (61852561957760130711/50000000000000000000 : ℝ)^32 ≤ (10541875339356501/10000000000000000 : ℝ)^129 := by
      have hnat : (61852561957760130711 : ℕ)^32*10000000000000000^129 ≤ 10541875339356501^129*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        61852561957760130711 50000000000000000000 10541875339356501 10000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10541875339356501/10000000000000000 : ℝ)) (X := (61852561957760130711/50000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s3_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(140877001693983/2945900000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(52024267193707/1178360000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (29459/50000 : ℝ)) (alpha := (140877001693983/2945900000000000 : ℝ)) (beta := (52024267193707/1178360000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow2,s3_corner2a]) (by linarith only [s3_pow2,s3_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, false]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (29459/50000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(140877001693983/2945900000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(52024267193707/1178360000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s3_0 : ((-452776867/1250000000 : ℝ)*X 0 0+(3501064587/10000000000 : ℝ)*X 0 1+(-292693809/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301058_s3_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_1 : ((3272907507/10000000000 : ℝ)*X 1 0+(-393890379/1250000000 : ℝ)*X 1 1+(-1285916061/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301058_s3_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_2 : ((5536709699/10000000000 : ℝ)*X 2 0+(1072657719/2000000000 : ℝ)*X 2 1+(460180627/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301058_s3_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_7 : ((-3099336317/10000000000 : ℝ)*X 0 0+(10988601/40000000 : ℝ)*X 0 1+(-1718939313/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301058_s3_s3_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_8 : ((3258869161/10000000000 : ℝ)*X 1 0+(-6976561/25000000 : ℝ)*X 1 1+(-6718859237/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301058_s3_s3_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_9 : ((5513195389/10000000000 : ℝ)*X 2 0+(2856031093/5000000000 : ℝ)*X 2 1+(1352071517/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301058_s3_s3_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_13 : ((4030467401/10000000000 : ℝ)*X 0 0+(7565721461/10000000000 : ℝ)*X 0 1+(-304367771/10000000000 : ℝ)*X 0 2+(4030467401/10000000000 : ℝ)*X 1 0+(7565721461/10000000000 : ℝ)*X 1 1+(-304367771/10000000000 : ℝ)*X 1 2+(4030467401/10000000000 : ℝ)*X 2 0+(7565721461/10000000000 : ℝ)*X 2 1+(-304367771/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301058_s3_s3_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_14 : ((-284072307/1000000000 : ℝ)*X 0 0+(1537610261/5000000000 : ℝ)*X 0 1+(-6824529357/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301058_s3_s3_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_15 : ((284072307/1000000000 : ℝ)*X 1 0+(-1537610261/5000000000 : ℝ)*X 1 1+(-6824529357/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301058_s3_s3_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_16 : ((623894647/1000000000 : ℝ)*X 2 0+(1300509613/2500000000 : ℝ)*X 2 1+(241121063/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301058_s3_s3_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_19 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 1 2+(-1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301058_s3_s3_19 p hpa hpb (pair X 2)
    change _ ≤ P 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_20 : ((623894647/1000000000 : ℝ)*X 0 0+(1300509613/2500000000 : ℝ)*X 0 1+(-241121063/2500000000 : ℝ)*X 0 2+(623894647/1000000000 : ℝ)*X 1 0+(1300509613/2500000000 : ℝ)*X 1 1+(-241121063/2500000000 : ℝ)*X 1 2+(623894647/1000000000 : ℝ)*X 2 0+(1300509613/2500000000 : ℝ)*X 2 1+(-241121063/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301058_s3_s3_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_21 : ((-3544973567/10000000000 : ℝ)*X 0 0+(862195069/2500000000 : ℝ)*X 0 1+(-745430581/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301058_s3_s3_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_22 : ((1699398727/5000000000 : ℝ)*X 1 0+(-650068047/2000000000 : ℝ)*X 1 1+(-6248122761/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301058_s3_s3_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_23 : ((1315014161/2000000000 : ℝ)*X 2 0+(842267229/2000000000 : ℝ)*X 2 1+(941082411/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301058_s3_s3_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_27 : ((155421003/500000000 : ℝ)*X 0 0+(8216889053/10000000000 : ℝ)*X 0 1+(-465641381/10000000000 : ℝ)*X 0 2+(155421003/500000000 : ℝ)*X 1 0+(8216889053/10000000000 : ℝ)*X 1 1+(-465641381/10000000000 : ℝ)*X 1 2+(155421003/500000000 : ℝ)*X 2 0+(8216889053/10000000000 : ℝ)*X 2 1+(-465641381/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301058_s3_s3_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s3_0 : (0 : ℝ) ≤ ((25211/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(25211/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (2584431877850937931394420541/286725344950000000000000000000000 : ℝ) := by norm_num
    linear_combination (8023744123/250000000000 : ℝ)*(base5) + (485953/200000000000 : ℝ)*(base49) + (323659/31250000000 : ℝ)*(base59) + (280807640079/250000000000 : ℝ)*(base60) + (3251841397067/500000000000 : ℝ)*(major_s3_0) + (3251841397067/500000000000 : ℝ)*(major_s3_1) + (3251841397067/500000000000 : ℝ)*(major_s3_2) + (61087997/1000000000000 : ℝ)*(sp_s3_1) + (8610724584391/1000000000000 : ℝ)*(sp_s3_7) + (2152640299113/250000000000 : ℝ)*(sp_s3_8) + (4321409780441/500000000000 : ℝ)*(sp_s3_9) + (1091092443013/250000000000 : ℝ)*(sp_s3_13) + (51149971/500000000000 : ℝ)*(sp_s3_15) + (17325079/100000000000 : ℝ)*(sp_s3_27) + (2198318999667/500000000000 : ℝ)*(f.failure) + (8610724584391/1000000000000 : ℝ)*(f.sum) + (25822394461016042843/52309609825000000000000000000000 : ℝ)*base63 + (236887945148087/589180000000000000000000000 : ℝ)*base64 + (1244638193377713/1775675000000000000000000000 : ℝ)*base67 + (32795849159773/736475000000000000000000000 : ℝ)*base68 + (27477187185404631613/237843128300000000000000000000000 : ℝ)*base71 + (2257880873568981/4036850000000000000000000000 : ℝ)*base73 + (213980897180497/887837500000000000000000000 : ℝ)*base74 + (84761135025083/504606250000000000000000000 : ℝ)*base76 + (119293823466401459/1120020878710937500000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base84 + (10327/12500000000000000 : ℝ)*base87 + (10327/12500000000000000 : ℝ)*base89 + (10327/12500000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s3_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(21733/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(21733/50000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (702931484891168133572976267/143362672475000000000000000000000 : ℝ) := by norm_num
    linear_combination (455705314917/125000000000 : ℝ)*(base5) + (6214554727/50000000000 : ℝ)*(base49) + (3182843034271/1000000000000 : ℝ)*(base60) + (5983435082209/1000000000000 : ℝ)*(major_s3_0) + (5983435082209/1000000000000 : ℝ)*(major_s3_1) + (3147828081107/500000000000 : ℝ)*(major_s3_2) + (37015453/500000000000 : ℝ)*(sp_s3_1) + (3955217/125000000000 : ℝ)*(sp_s3_9) + (3960964928661/500000000000 : ℝ)*(sp_s3_14) + (99022690917/12500000000 : ℝ)*(sp_s3_15) + (11567540734921/1000000000000 : ℝ)*(sp_s3_16) + (62444216001/200000000000 : ℝ)*(sp_s3_19) + (399296153367/1000000000000 : ℝ)*(sp_s3_20) + (1267283/31250000000 : ℝ)*(sp_s3_22) + (4044938672703/1000000000000 : ℝ)*(f.failure) + (3960964928661/500000000000 : ℝ)*(f.sum) + (4850031494083986323/52309609825000000000000000000000 : ℝ)*base63 + (8439559298439/23567200000000000000000000 : ℝ)*base64 + (96841926341983/1775675000000000000000000000 : ℝ)*base67 + (495703528995701/1472950000000000000000000000 : ℝ)*base68 + (18923740721825070723/237843128300000000000000000000000 : ℝ)*base71 + (953354400026153/2018425000000000000000000000 : ℝ)*base73 + (380382947299097/3551350000000000000000000000 : ℝ)*base75 + (429345185027081/4036850000000000000000000000 : ℝ)*base77 + (13245562645233865907/35840668118750000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base84 + (4643/25000000000000000 : ℝ)*base87 + (4643/25000000000000000 : ℝ)*base89 + (4643/25000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s3_2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-19721/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(-19721/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (40888487381219810395258593/8960167029687500000000000000000 : ℝ) := by norm_num
    linear_combination (2857393/1000000000000 : ℝ)*(base5) + (363479/500000000000 : ℝ)*(base16) + (112436343133/500000000000 : ℝ)*(base49) + (7707059429/62500000000 : ℝ)*(base60) + (3846321158111/1000000000000 : ℝ)*(major_s3_0) + (3846321158111/1000000000000 : ℝ)*(major_s3_1) + (3846321158111/1000000000000 : ℝ)*(major_s3_2) + (23948423/200000000000 : ℝ)*(sp_s3_0) + (7888679/200000000000 : ℝ)*(sp_s3_2) + (44680861/1000000000000 : ℝ)*(sp_s3_13) + (318270010457/62500000000 : ℝ)*(sp_s3_21) + (5092439182469/1000000000000 : ℝ)*(sp_s3_22) + (203696132937/40000000000 : ℝ)*(sp_s3_23) + (260015334741/100000000000 : ℝ)*(sp_s3_27) + (520040177133/200000000000 : ℝ)*(f.failure) + (1273109977357/250000000000 : ℝ)*(f.sum) + (30518783885130778747/209238439300000000000000000000000 : ℝ)*base62 + (781113804747429/1178360000000000000000000000 : ℝ)*base65 + (2849696572554761/3551350000000000000000000000 : ℝ)*base66 + (627243461711557/2945900000000000000000000000 : ℝ)*base69 + (32974429028736545971/475686256600000000000000000000000 : ℝ)*base70 + (462715915584463/2018425000000000000000000000 : ℝ)*base72 + (1421369115728869/1775675000000000000000000000 : ℝ)*base75 + (2070557770000447/2018425000000000000000000000 : ℝ)*base77 + (65550028189257198679/286725344950000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base80 + (1/1000000000000 : ℝ)*base82 + (1/1000000000000 : ℝ)*base84 + (473/5000000000000000 : ℝ)*base87 + (473/5000000000000000 : ℝ)*base89 + (473/5000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  exact ⟨ratio_s3_0,ratio_s3_1,ratio_s3_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (36981/25000 : ℝ) (92391/50000 : ℝ) (4759/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, false]])
    (hprev2 : (0 : ℝ) ≤ ((80737/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(80737/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(71027/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(71027/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-29459/50000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(-29459/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((25211/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(25211/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(21733/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(21733/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-19721/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(-19721/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c301058_s3 p hpa hpb X hX hprev2

#print axioms solution
