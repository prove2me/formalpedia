-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1098_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:59:37.343515+00:00
-- url     : https://prove2.me/submissions/9ce7fbfc-119c-4731-b450-57b8569b58fa

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_majorant
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
theorem frame_box_of_interval_base {p k A d ell u v w rho lo : ℝ}
    (base : ∀ X : Fin 3 → Fin 3 → ℝ, Frame p k A d X →
      (∀ i h, i ≠ h → 0 ≤ pair X i h) →
      (∀ i h, i ≠ h → |pair X i h| ≤ rho*pair X i i) →
      (∀ i h, i ≠ h → lo*pair X i i ≤ pair X i h) →
      -u ≤ X 0 0 ∧ X 0 0 ≤ -ell ∧ v ≤ X 0 1 ∧ X 0 1 ≤ w)
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p k A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ rho*pair X i i)
    (hlower : ∀ i h, i ≠ h → lo*pair X i i ≤ pair X i h) :
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
    · intro i j hij
      rw [pair_relabel]
      exact hlower (e i) (e j) (e.injective.ne hij)
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

theorem frame_interval_of_base {p k A d rho lo R L : ℝ}
    (base : ∀ X : Fin 3 → Fin 3 → ℝ, Frame p k A d X →
      (∀ i h, i ≠ h → 0 ≤ pair X i h) →
      (∀ i h, i ≠ h → |pair X i h| ≤ rho*pair X i i) →
      (∀ i h, i ≠ h → lo*pair X i i ≤ pair X i h) →
      L*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ R*pair X 0 0)
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p k A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ rho*pair X i i)
    (hlower : ∀ i h, i ≠ h → lo*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → L*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ R*pair X i i := by
  have permuted (e : Equiv.Perm (Fin 3)) :
      L*pair X (e 0) (e 0) ≤ pair X (e 0) (e 1) ∧
        pair X (e 0) (e 1) ≤ R*pair X (e 0) (e 0) := by
    have hh := base (relabel e X) (frame_relabel hX e)
      (fun i j hij => by rw [pair_relabel];exact hsign (e i) (e j) (e.injective.ne hij))
      (fun i j hij => by rw [pair_relabel];exact hratio (e i) (e j) (e.injective.ne hij))
      (fun i j hij => by rw [pair_relabel];exact hlower (e i) (e j) (e.injective.ne hij))
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


theorem rectangle_pair_majorant {p a lo hi c alpha : ℝ}
    (hp : 1 ≤ p) (ha : 0 < a) (hap : a ≤ p)
    (hlo : 0 ≤ lo) (hlohi : lo < hi) (hhi : hi ≤ 1) (halpha : 0 ≤ alpha)
    (hc : 1 ≤ c+2*alpha*lo)
    (hcorner00 : 1+2*lo^a ≤ (c+2*alpha*lo)^a)
    (hcorner10 : 1+hi^a+lo^a ≤ (c+alpha*(hi+lo))^a)
    (hcorner11 : 1+2*hi^a ≤ (c+2*alpha*hi)^a)
    (X : Fin 3 → Fin 3 → ℝ)
    (hmain : ∀ i, 0 ≤ pair X i i)
    (hlower : ∀ i h, i ≠ h → lo*pair X i i ≤ pair X i h)
    (hupper : ∀ i h, i ≠ h → |pair X i h| ≤ hi*pair X i i)
    (i j l : Fin 3) (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) :
    lpNorm p (pair X i) ≤ c*pair X i i+alpha*(pair X i j+pair X i l) := by
  have hh := rectangle_majorant hp ha hap hlo hlohi hhi halpha hc hcorner00 hcorner10 hcorner11
    (hmain i) (hlower i j hij) ((le_abs_self _).trans (hupper i j hij))
    (hlower i l hil) ((le_abs_self _).trans (hupper i l hil))
  have he : lpNorm p (pair X i) =
      (|pair X i i|^p+|pair X i j|^p+|pair X i l|^p)^(1/p) := by
    simp only [lpNorm,Real.norm_eq_abs]
    congr 1
    fin_cases i <;> fin_cases j <;> fin_cases l <;> try contradiction
    all_goals simp [Fin.sum_univ_three] <;> ring
  rw [he]
  exact hh

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
theorem support_rectangle_w1098_s9_0 (p : ℝ) (hpa : (4145/1024 : ℝ) ≤ p) (hpb : p ≤ (8291/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-273514151/1250000000 : ℝ)*x 0 + (2696881797/5000000000 : ℝ)*x 1 + (5265053091/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (273514151/1250000000 : ℝ)^8291 ≤ (2658345252959/20000000000000 : ℝ)^6243 := by
    have hnat : (273514151 : ℕ)^8291*20000000000000^6243 ≤ 2658345252959^6243*1250000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      273514151 1250000000 2658345252959 20000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2696881797/5000000000 : ℝ)^8291 ≤ (11012343515023/25000000000000 : ℝ)^6243 := by
    have hnat : (2696881797 : ℕ)^8291*25000000000000^6243 ≤ 11012343515023^6243*5000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696881797 5000000000 11012343515023 25000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265053091/10000000000 : ℝ)^8291 ≤ (10664724918421/25000000000000 : ℝ)^6243 := by
    have hnat : (5265053091 : ℕ)^8291*25000000000000^6243 ≤ 10664724918421^6243*10000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265053091 10000000000 10664724918421 25000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8291/2048 : ℝ)) 8291 6243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-273514151/1250000000 : ℝ), (2696881797/5000000000 : ℝ), (5265053091/10000000000 : ℝ)] ![(2658345252959/20000000000000 : ℝ), (11012343515023/25000000000000 : ℝ), (10664724918421/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-273514151/1250000000 : ℝ)|^8291 ≤ (2658345252959/20000000000000 : ℝ)^6243
        have hw : |(-273514151/1250000000 : ℝ)|=(273514151/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2696881797/5000000000 : ℝ)|^8291 ≤ (11012343515023/25000000000000 : ℝ)^6243
        have hw : |(2696881797/5000000000 : ℝ)|=(2696881797/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265053091/10000000000 : ℝ)|^8291 ≤ (10664724918421/25000000000000 : ℝ)^6243
        have hw : |(5265053091/10000000000 : ℝ)|=(5265053091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1098_s9_1 (p : ℝ) (hpa : (4145/1024 : ℝ) ≤ p) (hpb : p ≤ (8291/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1336221879/2500000000 : ℝ)*x 0 + (-281675959/1250000000 : ℝ)*x 1 + (2632526681/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336221879/2500000000 : ℝ)^8291 ≤ (1740802544447/4000000000000 : ℝ)^6243 := by
    have hnat : (1336221879 : ℕ)^8291*4000000000000^6243 ≤ 1740802544447^6243*2500000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336221879 2500000000 1740802544447 4000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (281675959/1250000000 : ℝ)^8291 ≤ (13821033792169/100000000000000 : ℝ)^6243 := by
    have hnat : (281675959 : ℕ)^8291*100000000000000^6243 ≤ 13821033792169^6243*1250000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      281675959 1250000000 13821033792169 100000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632526681/5000000000 : ℝ)^8291 ≤ (42658902589699/100000000000000 : ℝ)^6243 := by
    have hnat : (2632526681 : ℕ)^8291*100000000000000^6243 ≤ 42658902589699^6243*5000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632526681 5000000000 42658902589699 100000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8291/2048 : ℝ)) 8291 6243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336221879/2500000000 : ℝ), (-281675959/1250000000 : ℝ), (2632526681/5000000000 : ℝ)] ![(1740802544447/4000000000000 : ℝ), (13821033792169/100000000000000 : ℝ), (42658902589699/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336221879/2500000000 : ℝ)|^8291 ≤ (1740802544447/4000000000000 : ℝ)^6243
        have hw : |(1336221879/2500000000 : ℝ)|=(1336221879/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-281675959/1250000000 : ℝ)|^8291 ≤ (13821033792169/100000000000000 : ℝ)^6243
        have hw : |(-281675959/1250000000 : ℝ)|=(281675959/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632526681/5000000000 : ℝ)|^8291 ≤ (42658902589699/100000000000000 : ℝ)^6243
        have hw : |(2632526681/5000000000 : ℝ)|=(2632526681/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1098_s9_2 (p : ℝ) (hpa : (4145/1024 : ℝ) ≤ p) (hpb : p ≤ (8291/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (534488771/1000000000 : ℝ)*x 0 + (263252657/500000000 : ℝ)*x 1 + (-2253407707/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534488771/1000000000 : ℝ)^8291 ≤ (21760032854493/50000000000000 : ℝ)^6243 := by
    have hnat : (534488771 : ℕ)^8291*50000000000000^6243 ≤ 21760032854493^6243*1000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534488771 1000000000 21760032854493 50000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (263252657/500000000 : ℝ)^8291 ≤ (21329450100467/50000000000000 : ℝ)^6243 := by
    have hnat : (263252657 : ℕ)^8291*50000000000000^6243 ≤ 21329450100467^6243*500000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263252657 500000000 21329450100467 50000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2253407707/10000000000 : ℝ)^8291 ≤ (691051703863/5000000000000 : ℝ)^6243 := by
    have hnat : (2253407707 : ℕ)^8291*5000000000000^6243 ≤ 691051703863^6243*10000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2253407707 10000000000 691051703863 5000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8291/2048 : ℝ)) 8291 6243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(534488771/1000000000 : ℝ), (263252657/500000000 : ℝ), (-2253407707/10000000000 : ℝ)] ![(21760032854493/50000000000000 : ℝ), (21329450100467/50000000000000 : ℝ), (691051703863/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(534488771/1000000000 : ℝ)|^8291 ≤ (21760032854493/50000000000000 : ℝ)^6243
        have hw : |(534488771/1000000000 : ℝ)|=(534488771/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(263252657/500000000 : ℝ)|^8291 ≤ (21329450100467/50000000000000 : ℝ)^6243
        have hw : |(263252657/500000000 : ℝ)|=(263252657/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2253407707/10000000000 : ℝ)|^8291 ≤ (691051703863/5000000000000 : ℝ)^6243
        have hw : |(-2253407707/10000000000 : ℝ)|=(2253407707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1098_s9_3 (p : ℝ) (hpa : (4145/1024 : ℝ) ≤ p) (hpb : p ≤ (8291/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (54636397/125000000 : ℝ)*x 0 + (4245835827/10000000000 : ℝ)*x 1 + (140615413/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (54636397/125000000 : ℝ)^8291 ≤ (33316749711167/100000000000000 : ℝ)^6243 := by
    have hnat : (54636397 : ℕ)^8291*100000000000000^6243 ≤ 33316749711167^6243*125000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      54636397 125000000 33316749711167 100000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4245835827/10000000000 : ℝ)^8291 ≤ (4007075263299/12500000000000 : ℝ)^6243 := by
    have hnat : (4245835827 : ℕ)^8291*12500000000000^6243 ≤ 4007075263299^6243*10000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4245835827 10000000000 4007075263299 12500000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (140615413/312500000 : ℝ)^8291 ≤ (17313324085787/50000000000000 : ℝ)^6243 := by
    have hnat : (140615413 : ℕ)^8291*50000000000000^6243 ≤ 17313324085787^6243*312500000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      140615413 312500000 17313324085787 50000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8291/2048 : ℝ)) 8291 6243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(54636397/125000000 : ℝ), (4245835827/10000000000 : ℝ), (140615413/312500000 : ℝ)] ![(33316749711167/100000000000000 : ℝ), (4007075263299/12500000000000 : ℝ), (17313324085787/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(54636397/125000000 : ℝ)|^8291 ≤ (33316749711167/100000000000000 : ℝ)^6243
        have hw : |(54636397/125000000 : ℝ)|=(54636397/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4245835827/10000000000 : ℝ)|^8291 ≤ (4007075263299/12500000000000 : ℝ)^6243
        have hw : |(4245835827/10000000000 : ℝ)|=(4245835827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(140615413/312500000 : ℝ)|^8291 ≤ (17313324085787/50000000000000 : ℝ)^6243
        have hw : |(140615413/312500000 : ℝ)|=(140615413/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1098_s9_4 (p : ℝ) (hpa : (4145/1024 : ℝ) ≤ p) (hpb : p ≤ (8291/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-109405913/500000000 : ℝ)*x 0 + (5265376391/10000000000 : ℝ)*x 1 + (134835977/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (109405913/500000000 : ℝ)^8291 ≤ (13291767020527/100000000000000 : ℝ)^6243 := by
    have hnat : (109405913 : ℕ)^8291*100000000000000^6243 ≤ 13291767020527^6243*500000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      109405913 500000000 13291767020527 100000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265376391/10000000000 : ℝ)^8291 ≤ (4266237848243/10000000000000 : ℝ)^6243 := by
    have hnat : (5265376391 : ℕ)^8291*10000000000000^6243 ≤ 4266237848243^6243*10000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265376391 10000000000 4266237848243 10000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (134835977/250000000 : ℝ)^8291 ≤ (44045854482323/100000000000000 : ℝ)^6243 := by
    have hnat : (134835977 : ℕ)^8291*100000000000000^6243 ≤ 44045854482323^6243*250000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      134835977 250000000 44045854482323 100000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8291/2048 : ℝ)) 8291 6243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-109405913/500000000 : ℝ), (5265376391/10000000000 : ℝ), (134835977/250000000 : ℝ)] ![(13291767020527/100000000000000 : ℝ), (4266237848243/10000000000000 : ℝ), (44045854482323/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-109405913/500000000 : ℝ)|^8291 ≤ (13291767020527/100000000000000 : ℝ)^6243
        have hw : |(-109405913/500000000 : ℝ)|=(109405913/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265376391/10000000000 : ℝ)|^8291 ≤ (4266237848243/10000000000000 : ℝ)^6243
        have hw : |(5265376391/10000000000 : ℝ)|=(5265376391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(134835977/250000000 : ℝ)|^8291 ≤ (44045854482323/100000000000000 : ℝ)^6243
        have hw : |(134835977/250000000 : ℝ)|=(134835977/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1098_s9_5 (p : ℝ) (hpa : (4145/1024 : ℝ) ≤ p) (hpb : p ≤ (8291/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4370920917/10000000000 : ℝ)*x 0 + (562382173/1250000000 : ℝ)*x 1 + (1061618653/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4370920917/10000000000 : ℝ)^8291 ≤ (8329210601607/25000000000000 : ℝ)^6243 := by
    have hnat : (4370920917 : ℕ)^8291*25000000000000^6243 ≤ 8329210601607^6243*10000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4370920917 10000000000 8329210601607 25000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (562382173/1250000000 : ℝ)^8291 ≤ (34620150265277/100000000000000 : ℝ)^6243 := by
    have hnat : (562382173 : ℕ)^8291*100000000000000^6243 ≤ 34620150265277^6243*1250000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      562382173 1250000000 34620150265277 100000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1061618653/2500000000 : ℝ)^8291 ≤ (8015751828813/25000000000000 : ℝ)^6243 := by
    have hnat : (1061618653 : ℕ)^8291*25000000000000^6243 ≤ 8015751828813^6243*2500000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061618653 2500000000 8015751828813 25000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8291/2048 : ℝ)) 8291 6243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4370920917/10000000000 : ℝ), (562382173/1250000000 : ℝ), (1061618653/2500000000 : ℝ)] ![(8329210601607/25000000000000 : ℝ), (34620150265277/100000000000000 : ℝ), (8015751828813/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4370920917/10000000000 : ℝ)|^8291 ≤ (8329210601607/25000000000000 : ℝ)^6243
        have hw : |(4370920917/10000000000 : ℝ)|=(4370920917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(562382173/1250000000 : ℝ)|^8291 ≤ (34620150265277/100000000000000 : ℝ)^6243
        have hw : |(562382173/1250000000 : ℝ)|=(562382173/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1061618653/2500000000 : ℝ)|^8291 ≤ (8015751828813/25000000000000 : ℝ)^6243
        have hw : |(1061618653/2500000000 : ℝ)|=(1061618653/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1098_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4145/1024 : ℝ) ≤ p) (hpb : p ≤ (8291/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148615943/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7011/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2259/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (353/3125 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7011/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7011/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2259/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7011/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2259/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7011/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2259/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7011/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2259/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7011/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2259/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7011/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2259/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hlower 2 1 (by decide)
  have fm0 := f.main 0
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm0
  have fx01 := abs_le.mp (f.maximal 0 1)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx01
  have fx02 := abs_le.mp (f.maximal 0 2)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx02
  have fm1 := f.main 1
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm1
  have fx10 := abs_le.mp (f.maximal 1 0)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx10
  have fx12 := abs_le.mp (f.maximal 1 2)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx12
  have fm2 := f.main 2
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm2
  have fx20 := abs_le.mp (f.maximal 2 0)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx20
  have fx21 := abs_le.mp (f.maximal 2 1)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx21
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base65 : ((1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).2]
  have base66 : ((-1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).1]
  have base67 : ((1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).2]
  have base68 : ((-1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).1]
  have base69 : ((1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).2]
  have base70 : ((-1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).1]
  have base71 : ((1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).2]
  have base72 : ((-1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).1]
  have base73 : ((1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).2]
  have base74 : ((-1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).1]
  have base75 : ((1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).2]
  have base76 : ((-1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).1]
  have base77 : ((1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).2]
  have base78 : ((-1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).1]
  have base79 : ((1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).2]
  have base80 : ((-1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).1]
  have base81 : ((1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).2]
  have base82 : ((-1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).1]
  have base83 : ((1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).2]
  have base84 : ((-1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).1]
  have base85 : ((1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).2]
  have base86 : ((-1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).1]
  have base87 : ((1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).2]
  have base88 : ((-1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).1]
  have base89 : ((1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).2]
  have base90 : ((-1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).1]
  have base91 : ((1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).2]
  have base92 : ((-1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).1]
  have base93 : ((1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).2]
  have base94 : ((-1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).1]
  have base95 : ((1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.2]
  have base96 : ((-1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.1]
  have hpowlo : (2259/20000 : ℝ) ^ (4145/1024 : ℝ) ≤ (14663041627747841/100000000000000000000 : ℝ) := by
    have hpowers : (2259/20000 : ℝ)^4145 ≤ (14663041627747841/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2259 : ℕ)^4145*100000000000000000000^1024 ≤ 14663041627747841^1024*20000^4145 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2259 20000 14663041627747841 100000000000000000000 4145 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2259/20000 : ℝ)) (X := (14663041627747841/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4145 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7011/50000 : ℝ) ^ (4145/1024 : ℝ) ≤ (17594761288265837/50000000000000000000 : ℝ) := by
    have hpowers : (7011/50000 : ℝ)^4145 ≤ (17594761288265837/50000000000000000000 : ℝ)^1024 := by
      have hnat : (7011 : ℕ)^4145*50000000000000000000^1024 ≤ 17594761288265837^1024*50000^4145 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7011 50000 17594761288265837 50000000000000000000 4145 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7011/50000 : ℝ)) (X := (17594761288265837/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4145 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014663041627747841/50000000000000000000 : ℝ) ≤ (5000362202585461/5000000000000000 : ℝ) ^ (4145/1024 : ℝ) := by
    have hpowers : (50014663041627747841/50000000000000000000 : ℝ)^1024 ≤ (5000362202585461/5000000000000000 : ℝ)^4145 := by
      have hnat : (50014663041627747841 : ℕ)^1024*5000000000000000^4145 ≤ 5000362202585461^4145*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014663041627747841 50000000000000000000 5000362202585461 5000000000000000 1024 4145 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000362202585461/5000000000000000 : ℝ)) (X := (50014663041627747841/50000000000000000000 : ℝ)) (by norm_num) 4145 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20009970512840855903/20000000000000000000 : ℝ) ≤ (10001231349757807/10000000000000000 : ℝ) ^ (4145/1024 : ℝ) := by
    have hpowers : (20009970512840855903/20000000000000000000 : ℝ)^1024 ≤ (10001231349757807/10000000000000000 : ℝ)^4145 := by
      have hnat : (20009970512840855903 : ℕ)^1024*10000000000000000^4145 ≤ 10001231349757807^4145*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20009970512840855903 20000000000000000000 10001231349757807 10000000000000000 1024 4145 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001231349757807/10000000000000000 : ℝ)) (X := (20009970512840855903/20000000000000000000 : ℝ)) (by norm_num) 4145 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25017594761288265837/25000000000000000000 : ℝ) ≤ (2500434573586173/2500000000000000 : ℝ) ^ (4145/1024 : ℝ) := by
    have hpowers : (25017594761288265837/25000000000000000000 : ℝ)^1024 ≤ (2500434573586173/2500000000000000 : ℝ)^4145 := by
      have hnat : (25017594761288265837 : ℕ)^1024*2500000000000000^4145 ≤ 2500434573586173^4145*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25017594761288265837 25000000000000000000 2500434573586173 2500000000000000 1024 4145 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500434573586173/2500000000000000 : ℝ)) (X := (25017594761288265837/25000000000000000000 : ℝ)) (by norm_num) 4145 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14663041627747841/100000000000000000000 : ℝ) ≤ ((189309191490856751/189375000000000000 : ℝ)+2*(101388917377/54540000000000 : ℝ)*(2259/20000 : ℝ))^(4145/1024 : ℝ) := by
    rw [show (189309191490856751/189375000000000000 : ℝ)+2*(101388917377/54540000000000 : ℝ)*(2259/20000 : ℝ)=(5000362202585461/5000000000000000 : ℝ) by norm_num, show 1+2*(14663041627747841/100000000000000000000 : ℝ)=(50014663041627747841/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(17594761288265837/50000000000000000000 : ℝ)+(14663041627747841/100000000000000000000 : ℝ) ≤ ((189309191490856751/189375000000000000 : ℝ)+(101388917377/54540000000000 : ℝ)*((7011/50000 : ℝ)+(2259/20000 : ℝ)))^(4145/1024 : ℝ) := by
    rw [show (189309191490856751/189375000000000000 : ℝ)+(101388917377/54540000000000 : ℝ)*((7011/50000 : ℝ)+(2259/20000 : ℝ))=(10001231349757807/10000000000000000 : ℝ) by norm_num, show 1+(17594761288265837/50000000000000000000 : ℝ)+(14663041627747841/100000000000000000000 : ℝ)=(20009970512840855903/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(17594761288265837/50000000000000000000 : ℝ) ≤ ((189309191490856751/189375000000000000 : ℝ)+2*(101388917377/54540000000000 : ℝ)*(7011/50000 : ℝ))^(4145/1024 : ℝ) := by
    rw [show (189309191490856751/189375000000000000 : ℝ)+2*(101388917377/54540000000000 : ℝ)*(7011/50000 : ℝ)=(2500434573586173/2500000000000000 : ℝ) by norm_num, show 1+2*(17594761288265837/50000000000000000000 : ℝ)=(25017594761288265837/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (189309191490856751/189375000000000000 : ℝ)*(X 1 0+X 2 0)+(101388917377/54540000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4145/1024 : ℝ)) (lo := (2259/20000 : ℝ)) (hi := (7011/50000 : ℝ)) (c := (189309191490856751/189375000000000000 : ℝ)) (alpha := (101388917377/54540000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (189309191490856751/189375000000000000 : ℝ)*(X 0 1+X 2 1)+(101388917377/54540000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4145/1024 : ℝ)) (lo := (2259/20000 : ℝ)) (hi := (7011/50000 : ℝ)) (c := (189309191490856751/189375000000000000 : ℝ)) (alpha := (101388917377/54540000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (189309191490856751/189375000000000000 : ℝ)*(X 0 2+X 1 2)+(101388917377/54540000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4145/1024 : ℝ)) (lo := (2259/20000 : ℝ)) (hi := (7011/50000 : ℝ)) (c := (189309191490856751/189375000000000000 : ℝ)) (alpha := (101388917377/54540000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-273514151/1250000000 : ℝ)*X 0 0+(2696881797/5000000000 : ℝ)*X 0 1+(5265053091/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1098_s9_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1336221879/2500000000 : ℝ)*X 1 0+(-281675959/1250000000 : ℝ)*X 1 1+(2632526681/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1098_s9_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((534488771/1000000000 : ℝ)*X 2 0+(263252657/500000000 : ℝ)*X 2 1+(-2253407707/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1098_s9_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((54636397/125000000 : ℝ)*X 0 0+(4245835827/10000000000 : ℝ)*X 0 1+(140615413/312500000 : ℝ)*X 0 2+(54636397/125000000 : ℝ)*X 1 0+(4245835827/10000000000 : ℝ)*X 1 1+(140615413/312500000 : ℝ)*X 1 2+(54636397/125000000 : ℝ)*X 2 0+(4245835827/10000000000 : ℝ)*X 2 1+(140615413/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1098_s9_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-109405913/500000000 : ℝ)*X 0 0+(5265376391/10000000000 : ℝ)*X 0 1+(134835977/250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1098_s9_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((4370920917/10000000000 : ℝ)*X 0 0+(562382173/1250000000 : ℝ)*X 0 1+(1061618653/2500000000 : ℝ)*X 0 2+(4370920917/10000000000 : ℝ)*X 1 0+(562382173/1250000000 : ℝ)*X 1 1+(1061618653/2500000000 : ℝ)*X 1 2+(4370920917/10000000000 : ℝ)*X 2 0+(562382173/1250000000 : ℝ)*X 2 1+(1061618653/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1098_s9_5 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (8146534677131379638209291/2840625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (950452389/100000000000000 : ℝ)*(base19) + (1211253127/100000000000000 : ℝ)*(base23) + (151949491/100000000000000 : ℝ)*(upper3) + (11332253/100000000000000 : ℝ)*(upper4) + (33384731/25000000000000 : ℝ)*(upper5) + (146358714230147/2500000000000 : ℝ)*(major0) + (146358714230147/2500000000000 : ℝ)*(major1) + (146358714230147/2500000000000 : ℝ)*(major2) + (3884705383074403/50000000000000 : ℝ)*(sp0) + (7769449433473449/100000000000000 : ℝ)*(sp1) + (7769449172672711/100000000000000 : ℝ)*(sp2) + (1969616051864539/50000000000000 : ℝ)*(sp3) + (4952222129/12500000000000 : ℝ)*(sp4) + (3638790317/25000000000000 : ℝ)*(sp5) + (1969623329445173/50000000000000 : ℝ)*(f.failure) + (7769450383925837/100000000000000 : ℝ)*(f.sum) + (119966872669/681750000000000000000000000 : ℝ)*base66 + (40655546898097651/2130468750000000000000000000000 : ℝ)*base68 + (3927016503746681/532617187500000000000000000000 : ℝ)*base69 + (18876917539895323/4260937500000000000000000000000 : ℝ)*base71 + (1883697783787/272700000000000000000000000 : ℝ)*base74 + (94695019352533/16644287109375000000000000000 : ℝ)*base75 + (7736812631977349/2130468750000000000000000000000 : ℝ)*base77 + (36768580091021099/2130468750000000000000000000000 : ℝ)*base79 + (1806588766189/2727000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (52193139/5000000000000000000000 : ℝ)*base89 + (52193139/5000000000000000000000 : ℝ)*base91 + (52193139/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(upper0) + hcertificate_margin
theorem rectangle_w1098_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4145/1024 : ℝ) ≤ p) (hpb : p ≤ (8291/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148615943/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7011/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2259/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (353/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7011/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1098_s9 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1098_box_0 (p : ℝ) (hpa : (4145/1024 : ℝ) ≤ p) (hpb : p ≤ (8291/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-205975017/1000000000 : ℝ)*x 0 + (5376926347/10000000000 : ℝ)*x 1 + (537692659/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (205975017/1000000000 : ℝ)^8291 ≤ (12266288775759/100000000000000 : ℝ)^6243 := by
    have hnat : (205975017 : ℕ)^8291*100000000000000^6243 ≤ 12266288775759^6243*1000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      205975017 1000000000 12266288775759 100000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5376926347/10000000000 : ℝ)^8291 ≤ (43866854288143/100000000000000 : ℝ)^6243 := by
    have hnat : (5376926347 : ℕ)^8291*100000000000000^6243 ≤ 43866854288143^6243*10000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5376926347 10000000000 43866854288143 100000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (537692659/1000000000 : ℝ)^8291 ≤ (4386685692097/10000000000000 : ℝ)^6243 := by
    have hnat : (537692659 : ℕ)^8291*10000000000000^6243 ≤ 4386685692097^6243*1000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      537692659 1000000000 4386685692097 10000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8291/2048 : ℝ)) 8291 6243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-205975017/1000000000 : ℝ), (5376926347/10000000000 : ℝ), (537692659/1000000000 : ℝ)] ![(12266288775759/100000000000000 : ℝ), (43866854288143/100000000000000 : ℝ), (4386685692097/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-205975017/1000000000 : ℝ)|^8291 ≤ (12266288775759/100000000000000 : ℝ)^6243
        have hw : |(-205975017/1000000000 : ℝ)|=(205975017/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5376926347/10000000000 : ℝ)|^8291 ≤ (43866854288143/100000000000000 : ℝ)^6243
        have hw : |(5376926347/10000000000 : ℝ)|=(5376926347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(537692659/1000000000 : ℝ)|^8291 ≤ (4386685692097/10000000000000 : ℝ)^6243
        have hw : |(537692659/1000000000 : ℝ)|=(537692659/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1098_box_1 (p : ℝ) (hpa : (4145/1024 : ℝ) ≤ p) (hpb : p ≤ (8291/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2647776207/5000000000 : ℝ)*x 0 + (-1084997061/5000000000 : ℝ)*x 1 + (1075385299/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2647776207/5000000000 : ℝ)^8291 ≤ (42987390004961/100000000000000 : ℝ)^6243 := by
    have hnat : (2647776207 : ℕ)^8291*100000000000000^6243 ≤ 42987390004961^6243*5000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647776207 5000000000 42987390004961 100000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1084997061/5000000000 : ℝ)^8291 ≤ (13145754084213/100000000000000 : ℝ)^6243 := by
    have hnat : (1084997061 : ℕ)^8291*100000000000000^6243 ≤ 13145754084213^6243*5000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1084997061 5000000000 13145754084213 100000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1075385299/2000000000 : ℝ)^8291 ≤ (1754674235667/4000000000000 : ℝ)^6243 := by
    have hnat : (1075385299 : ℕ)^8291*4000000000000^6243 ≤ 1754674235667^6243*2000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1075385299 2000000000 1754674235667 4000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8291/2048 : ℝ)) 8291 6243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2647776207/5000000000 : ℝ), (-1084997061/5000000000 : ℝ), (1075385299/2000000000 : ℝ)] ![(42987390004961/100000000000000 : ℝ), (13145754084213/100000000000000 : ℝ), (1754674235667/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2647776207/5000000000 : ℝ)|^8291 ≤ (42987390004961/100000000000000 : ℝ)^6243
        have hw : |(2647776207/5000000000 : ℝ)|=(2647776207/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1084997061/5000000000 : ℝ)|^8291 ≤ (13145754084213/100000000000000 : ℝ)^6243
        have hw : |(-1084997061/5000000000 : ℝ)|=(1084997061/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1075385299/2000000000 : ℝ)|^8291 ≤ (1754674235667/4000000000000 : ℝ)^6243
        have hw : |(1075385299/2000000000 : ℝ)|=(1075385299/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1098_box_2 (p : ℝ) (hpa : (4145/1024 : ℝ) ≤ p) (hpb : p ≤ (8291/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5295552533/10000000000 : ℝ)*x 0 + (5376926531/10000000000 : ℝ)*x 1 + (-433998783/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5295552533/10000000000 : ℝ)^8291 ≤ (42987391287853/100000000000000 : ℝ)^6243 := by
    have hnat : (5295552533 : ℕ)^8291*100000000000000^6243 ≤ 42987391287853^6243*10000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5295552533 10000000000 42987391287853 100000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5376926531/10000000000 : ℝ)^8291 ≤ (10966714070431/25000000000000 : ℝ)^6243 := by
    have hnat : (5376926531 : ℕ)^8291*25000000000000^6243 ≤ 10966714070431^6243*10000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5376926531 10000000000 10966714070431 25000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (433998783/2000000000 : ℝ)^8291 ≤ (13145752418843/100000000000000 : ℝ)^6243 := by
    have hnat : (433998783 : ℕ)^8291*100000000000000^6243 ≤ 13145752418843^6243*2000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      433998783 2000000000 13145752418843 100000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8291/2048 : ℝ)) 8291 6243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5295552533/10000000000 : ℝ), (5376926531/10000000000 : ℝ), (-433998783/2000000000 : ℝ)] ![(42987391287853/100000000000000 : ℝ), (10966714070431/25000000000000 : ℝ), (13145752418843/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5295552533/10000000000 : ℝ)|^8291 ≤ (42987391287853/100000000000000 : ℝ)^6243
        have hw : |(5295552533/10000000000 : ℝ)|=(5295552533/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5376926531/10000000000 : ℝ)|^8291 ≤ (10966714070431/25000000000000 : ℝ)^6243
        have hw : |(5376926531/10000000000 : ℝ)|=(5376926531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-433998783/2000000000 : ℝ)|^8291 ≤ (13145752418843/100000000000000 : ℝ)^6243
        have hw : |(-433998783/2000000000 : ℝ)|=(433998783/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1098_box_3 (p : ℝ) (hpa : (4145/1024 : ℝ) ≤ p) (hpb : p ≤ (8291/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1119732677/2500000000 : ℝ)*x 0 + (172761627/400000000 : ℝ)*x 1 + (4319040653/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1119732677/2500000000 : ℝ)^8291 ≤ (34414620870047/100000000000000 : ℝ)^6243 := by
    have hnat : (1119732677 : ℕ)^8291*100000000000000^6243 ≤ 34414620870047^6243*2500000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1119732677 2500000000 34414620870047 100000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (172761627/400000000 : ℝ)^8291 ≤ (4099086208497/12500000000000 : ℝ)^6243 := by
    have hnat : (172761627 : ℕ)^8291*12500000000000^6243 ≤ 4099086208497^6243*400000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      172761627 400000000 4099086208497 12500000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4319040653/10000000000 : ℝ)^8291 ≤ (32792689446143/100000000000000 : ℝ)^6243 := by
    have hnat : (4319040653 : ℕ)^8291*100000000000000^6243 ≤ 32792689446143^6243*10000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4319040653 10000000000 32792689446143 100000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8291/2048 : ℝ)) 8291 6243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1119732677/2500000000 : ℝ), (172761627/400000000 : ℝ), (4319040653/10000000000 : ℝ)] ![(34414620870047/100000000000000 : ℝ), (4099086208497/12500000000000 : ℝ), (32792689446143/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1119732677/2500000000 : ℝ)|^8291 ≤ (34414620870047/100000000000000 : ℝ)^6243
        have hw : |(1119732677/2500000000 : ℝ)|=(1119732677/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(172761627/400000000 : ℝ)|^8291 ≤ (4099086208497/12500000000000 : ℝ)^6243
        have hw : |(172761627/400000000 : ℝ)|=(172761627/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4319040653/10000000000 : ℝ)|^8291 ≤ (32792689446143/100000000000000 : ℝ)^6243
        have hw : |(4319040653/10000000000 : ℝ)|=(4319040653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1098_box_4 (p : ℝ) (hpa : (4145/1024 : ℝ) ≤ p) (hpb : p ≤ (8291/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2317854561/10000000000 : ℝ)*x 0 + (1320138731/2500000000 : ℝ)*x 1 + (5280555399/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2317854561/10000000000 : ℝ)^8291 ≤ (2869685753769/20000000000000 : ℝ)^6243 := by
    have hnat : (2317854561 : ℕ)^8291*20000000000000^6243 ≤ 2869685753769^6243*10000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2317854561 10000000000 2869685753769 20000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1320138731/2500000000 : ℝ)^8291 ≤ (21412891524501/50000000000000 : ℝ)^6243 := by
    have hnat : (1320138731 : ℕ)^8291*50000000000000^6243 ≤ 21412891524501^6243*2500000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1320138731 2500000000 21412891524501 50000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5280555399/10000000000 : ℝ)^8291 ≤ (42825788165031/100000000000000 : ℝ)^6243 := by
    have hnat : (5280555399 : ℕ)^8291*100000000000000^6243 ≤ 42825788165031^6243*10000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5280555399 10000000000 42825788165031 100000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8291/2048 : ℝ)) 8291 6243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2317854561/10000000000 : ℝ), (1320138731/2500000000 : ℝ), (5280555399/10000000000 : ℝ)] ![(2869685753769/20000000000000 : ℝ), (21412891524501/50000000000000 : ℝ), (42825788165031/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2317854561/10000000000 : ℝ)|^8291 ≤ (2869685753769/20000000000000 : ℝ)^6243
        have hw : |(-2317854561/10000000000 : ℝ)|=(2317854561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1320138731/2500000000 : ℝ)|^8291 ≤ (21412891524501/50000000000000 : ℝ)^6243
        have hw : |(1320138731/2500000000 : ℝ)|=(1320138731/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5280555399/10000000000 : ℝ)|^8291 ≤ (42825788165031/100000000000000 : ℝ)^6243
        have hw : |(5280555399/10000000000 : ℝ)|=(5280555399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1098_box_5 (p : ℝ) (hpa : (4145/1024 : ℝ) ≤ p) (hpb : p ≤ (8291/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (53637063/100000000 : ℝ)*x 0 + (-1103885059/5000000000 : ℝ)*x 1 + (2640277613/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (53637063/100000000 : ℝ)^8291 ≤ (43723677139201/100000000000000 : ℝ)^6243 := by
    have hnat : (53637063 : ℕ)^8291*100000000000000^6243 ≤ 43723677139201^6243*100000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53637063 100000000 43723677139201 100000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1103885059/5000000000 : ℝ)^8291 ≤ (420329267057/3125000000000 : ℝ)^6243 := by
    have hnat : (1103885059 : ℕ)^8291*3125000000000^6243 ≤ 420329267057^6243*5000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1103885059 5000000000 420329267057 3125000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2640277613/5000000000 : ℝ)^8291 ≤ (42825786301719/100000000000000 : ℝ)^6243 := by
    have hnat : (2640277613 : ℕ)^8291*100000000000000^6243 ≤ 42825786301719^6243*5000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2640277613 5000000000 42825786301719 100000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8291/2048 : ℝ)) 8291 6243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(53637063/100000000 : ℝ), (-1103885059/5000000000 : ℝ), (2640277613/5000000000 : ℝ)] ![(43723677139201/100000000000000 : ℝ), (420329267057/3125000000000 : ℝ), (42825786301719/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(53637063/100000000 : ℝ)|^8291 ≤ (43723677139201/100000000000000 : ℝ)^6243
        have hw : |(53637063/100000000 : ℝ)|=(53637063/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1103885059/5000000000 : ℝ)|^8291 ≤ (420329267057/3125000000000 : ℝ)^6243
        have hw : |(-1103885059/5000000000 : ℝ)|=(1103885059/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2640277613/5000000000 : ℝ)|^8291 ≤ (42825786301719/100000000000000 : ℝ)^6243
        have hw : |(2640277613/5000000000 : ℝ)|=(2640277613/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1098_box_6 (p : ℝ) (hpa : (4145/1024 : ℝ) ≤ p) (hpb : p ≤ (8291/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5363706183/10000000000 : ℝ)*x 0 + (2640277839/5000000000 : ℝ)*x 1 + (-275971209/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5363706183/10000000000 : ℝ)^8291 ≤ (43723675872567/100000000000000 : ℝ)^6243 := by
    have hnat : (5363706183 : ℕ)^8291*100000000000000^6243 ≤ 43723675872567^6243*10000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5363706183 10000000000 43723675872567 100000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2640277839/5000000000 : ℝ)^8291 ≤ (5353223896253/12500000000000 : ℝ)^6243 := by
    have hnat : (2640277839 : ℕ)^8291*12500000000000^6243 ≤ 5353223896253^6243*5000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2640277839 5000000000 5353223896253 12500000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (275971209/1250000000 : ℝ)^8291 ≤ (6725266468631/50000000000000 : ℝ)^6243 := by
    have hnat : (275971209 : ℕ)^8291*50000000000000^6243 ≤ 6725266468631^6243*1250000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      275971209 1250000000 6725266468631 50000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8291/2048 : ℝ)) 8291 6243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5363706183/10000000000 : ℝ), (2640277839/5000000000 : ℝ), (-275971209/1250000000 : ℝ)] ![(43723675872567/100000000000000 : ℝ), (5353223896253/12500000000000 : ℝ), (6725266468631/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5363706183/10000000000 : ℝ)|^8291 ≤ (43723675872567/100000000000000 : ℝ)^6243
        have hw : |(5363706183/10000000000 : ℝ)|=(5363706183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2640277839/5000000000 : ℝ)|^8291 ≤ (5353223896253/12500000000000 : ℝ)^6243
        have hw : |(2640277839/5000000000 : ℝ)|=(2640277839/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-275971209/1250000000 : ℝ)|^8291 ≤ (6725266468631/50000000000000 : ℝ)^6243
        have hw : |(-275971209/1250000000 : ℝ)|=(275971209/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1098_box_7 (p : ℝ) (hpa : (4145/1024 : ℝ) ≤ p) (hpb : p ≤ (8291/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4262549271/10000000000 : ℝ)*x 0 + (2213605289/5000000000 : ℝ)*x 1 + (885441961/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4262549271/10000000000 : ℝ)^8291 ≤ (8056073676089/25000000000000 : ℝ)^6243 := by
    have hnat : (4262549271 : ℕ)^8291*25000000000000^6243 ≤ 8056073676089^6243*10000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4262549271 10000000000 8056073676089 25000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2213605289/5000000000 : ℝ)^8291 ≤ (6777571313659/20000000000000 : ℝ)^6243 := by
    have hnat : (2213605289 : ℕ)^8291*20000000000000^6243 ≤ 6777571313659^6243*5000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2213605289 5000000000 6777571313659 20000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (885441961/2000000000 : ℝ)^8291 ≤ (16943924355193/50000000000000 : ℝ)^6243 := by
    have hnat : (885441961 : ℕ)^8291*50000000000000^6243 ≤ 16943924355193^6243*2000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      885441961 2000000000 16943924355193 50000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8291/2048 : ℝ)) 8291 6243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4262549271/10000000000 : ℝ), (2213605289/5000000000 : ℝ), (885441961/2000000000 : ℝ)] ![(8056073676089/25000000000000 : ℝ), (6777571313659/20000000000000 : ℝ), (16943924355193/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4262549271/10000000000 : ℝ)|^8291 ≤ (8056073676089/25000000000000 : ℝ)^6243
        have hw : |(4262549271/10000000000 : ℝ)|=(4262549271/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2213605289/5000000000 : ℝ)|^8291 ≤ (6777571313659/20000000000000 : ℝ)^6243
        have hw : |(2213605289/5000000000 : ℝ)|=(2213605289/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(885441961/2000000000 : ℝ)|^8291 ≤ (16943924355193/50000000000000 : ℝ)^6243
        have hw : |(885441961/2000000000 : ℝ)|=(885441961/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1098_box_8 (p : ℝ) (hpa : (4145/1024 : ℝ) ≤ p) (hpb : p ≤ (8291/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-282991657/1250000000 : ℝ)*x 0 + (5215098981/10000000000 : ℝ)*x 1 + (5386530579/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (282991657/1250000000 : ℝ)^8291 ≤ (13906834881467/100000000000000 : ℝ)^6243 := by
    have hnat : (282991657 : ℕ)^8291*100000000000000^6243 ≤ 13906834881467^6243*1250000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      282991657 1250000000 13906834881467 100000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5215098981/10000000000 : ℝ)^8291 ≤ (10530555395883/25000000000000 : ℝ)^6243 := by
    have hnat : (5215098981 : ℕ)^8291*25000000000000^6243 ≤ 10530555395883^6243*10000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5215098981 10000000000 10530555395883 25000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5386530579/10000000000 : ℝ)^8291 ≤ (43970943518261/100000000000000 : ℝ)^6243 := by
    have hnat : (5386530579 : ℕ)^8291*100000000000000^6243 ≤ 43970943518261^6243*10000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5386530579 10000000000 43970943518261 100000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8291/2048 : ℝ)) 8291 6243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-282991657/1250000000 : ℝ), (5215098981/10000000000 : ℝ), (5386530579/10000000000 : ℝ)] ![(13906834881467/100000000000000 : ℝ), (10530555395883/25000000000000 : ℝ), (43970943518261/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-282991657/1250000000 : ℝ)|^8291 ≤ (13906834881467/100000000000000 : ℝ)^6243
        have hw : |(-282991657/1250000000 : ℝ)|=(282991657/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5215098981/10000000000 : ℝ)|^8291 ≤ (10530555395883/25000000000000 : ℝ)^6243
        have hw : |(5215098981/10000000000 : ℝ)|=(5215098981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5386530579/10000000000 : ℝ)|^8291 ≤ (43970943518261/100000000000000 : ℝ)^6243
        have hw : |(5386530579/10000000000 : ℝ)|=(5386530579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1098_box_9 (p : ℝ) (hpa : (4145/1024 : ℝ) ≤ p) (hpb : p ≤ (8291/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5288756737/10000000000 : ℝ)*x 0 + (-433231939/2000000000 : ℝ)*x 1 + (1077306089/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5288756737/10000000000 : ℝ)^8291 ≤ (42914143877973/100000000000000 : ℝ)^6243 := by
    have hnat : (5288756737 : ℕ)^8291*100000000000000^6243 ≤ 42914143877973^6243*10000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5288756737 10000000000 42914143877973 100000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (433231939/2000000000 : ℝ)^8291 ≤ (819682127201/6250000000000 : ℝ)^6243 := by
    have hnat : (433231939 : ℕ)^8291*6250000000000^6243 ≤ 819682127201^6243*2000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      433231939 2000000000 819682127201 6250000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1077306089/2000000000 : ℝ)^8291 ≤ (10992735516391/25000000000000 : ℝ)^6243 := by
    have hnat : (1077306089 : ℕ)^8291*25000000000000^6243 ≤ 10992735516391^6243*2000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1077306089 2000000000 10992735516391 25000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8291/2048 : ℝ)) 8291 6243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5288756737/10000000000 : ℝ), (-433231939/2000000000 : ℝ), (1077306089/2000000000 : ℝ)] ![(42914143877973/100000000000000 : ℝ), (819682127201/6250000000000 : ℝ), (10992735516391/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5288756737/10000000000 : ℝ)|^8291 ≤ (42914143877973/100000000000000 : ℝ)^6243
        have hw : |(5288756737/10000000000 : ℝ)|=(5288756737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-433231939/2000000000 : ℝ)|^8291 ≤ (819682127201/6250000000000 : ℝ)^6243
        have hw : |(-433231939/2000000000 : ℝ)|=(433231939/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1077306089/2000000000 : ℝ)|^8291 ≤ (10992735516391/25000000000000 : ℝ)^6243
        have hw : |(1077306089/2000000000 : ℝ)|=(1077306089/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1098_box_10 (p : ℝ) (hpa : (4145/1024 : ℝ) ≤ p) (hpb : p ≤ (8291/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (66109461/125000000 : ℝ)*x 0 + (5386530557/10000000000 : ℝ)*x 1 + (-2166159353/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (66109461/125000000 : ℝ)^8291 ≤ (42914145418951/100000000000000 : ℝ)^6243 := by
    have hnat : (66109461 : ℕ)^8291*100000000000000^6243 ≤ 42914145418951^6243*125000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66109461 125000000 42914145418951 100000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5386530557/10000000000 : ℝ)^8291 ≤ (21985471639879/50000000000000 : ℝ)^6243 := by
    have hnat : (5386530557 : ℕ)^8291*50000000000000^6243 ≤ 21985471639879^6243*10000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5386530557 10000000000 21985471639879 50000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2166159353/10000000000 : ℝ)^8291 ≤ (1311491128533/10000000000000 : ℝ)^6243 := by
    have hnat : (2166159353 : ℕ)^8291*10000000000000^6243 ≤ 1311491128533^6243*10000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2166159353 10000000000 1311491128533 10000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8291/2048 : ℝ)) 8291 6243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(66109461/125000000 : ℝ), (5386530557/10000000000 : ℝ), (-2166159353/10000000000 : ℝ)] ![(42914145418951/100000000000000 : ℝ), (21985471639879/50000000000000 : ℝ), (1311491128533/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(66109461/125000000 : ℝ)|^8291 ≤ (42914145418951/100000000000000 : ℝ)^6243
        have hw : |(66109461/125000000 : ℝ)|=(66109461/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5386530557/10000000000 : ℝ)|^8291 ≤ (21985471639879/50000000000000 : ℝ)^6243
        have hw : |(5386530557/10000000000 : ℝ)|=(5386530557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2166159353/10000000000 : ℝ)|^8291 ≤ (1311491128533/10000000000000 : ℝ)^6243
        have hw : |(-2166159353/10000000000 : ℝ)|=(2166159353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1098_box_11 (p : ℝ) (hpa : (4145/1024 : ℝ) ≤ p) (hpb : p ≤ (8291/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1125055469/2500000000 : ℝ)*x 0 + (4308254441/10000000000 : ℝ)*x 1 + (4308254681/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1125055469/2500000000 : ℝ)^8291 ≤ (34632051059389/100000000000000 : ℝ)^6243 := by
    have hnat : (1125055469 : ℕ)^8291*100000000000000^6243 ≤ 34632051059389^6243*2500000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1125055469 2500000000 34632051059389 100000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4308254441/10000000000 : ℝ)^8291 ≤ (4085496656461/12500000000000 : ℝ)^6243 := by
    have hnat : (4308254441 : ℕ)^8291*12500000000000^6243 ≤ 4085496656461^6243*10000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4308254441 10000000000 4085496656461 12500000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4308254681/10000000000 : ℝ)^8291 ≤ (326839756697/1000000000000 : ℝ)^6243 := by
    have hnat : (4308254681 : ℕ)^8291*1000000000000^6243 ≤ 326839756697^6243*10000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4308254681 10000000000 326839756697 1000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8291/2048 : ℝ)) 8291 6243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1125055469/2500000000 : ℝ), (4308254441/10000000000 : ℝ), (4308254681/10000000000 : ℝ)] ![(34632051059389/100000000000000 : ℝ), (4085496656461/12500000000000 : ℝ), (326839756697/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1125055469/2500000000 : ℝ)|^8291 ≤ (34632051059389/100000000000000 : ℝ)^6243
        have hw : |(1125055469/2500000000 : ℝ)|=(1125055469/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4308254441/10000000000 : ℝ)|^8291 ≤ (4085496656461/12500000000000 : ℝ)^6243
        have hw : |(4308254441/10000000000 : ℝ)|=(4308254441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4308254681/10000000000 : ℝ)|^8291 ≤ (326839756697/1000000000000 : ℝ)^6243
        have hw : |(4308254681/10000000000 : ℝ)|=(4308254681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1098_box_12 (p : ℝ) (hpa : (4145/1024 : ℝ) ≤ p) (hpb : p ≤ (8291/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2114018421/10000000000 : ℝ)*x 0 + (5441072203/10000000000 : ℝ)*x 1 + (1054507619/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2114018421/10000000000 : ℝ)^8291 ≤ (793583193307/6250000000000 : ℝ)^6243 := by
    have hnat : (2114018421 : ℕ)^8291*6250000000000^6243 ≤ 793583193307^6243*10000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2114018421 10000000000 793583193307 6250000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5441072203/10000000000 : ℝ)^8291 ≤ (44563210287067/100000000000000 : ℝ)^6243 := by
    have hnat : (5441072203 : ℕ)^8291*100000000000000^6243 ≤ 44563210287067^6243*10000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5441072203 10000000000 44563210287067 100000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1054507619/2000000000 : ℝ)^8291 ≤ (8547891722519/20000000000000 : ℝ)^6243 := by
    have hnat : (1054507619 : ℕ)^8291*20000000000000^6243 ≤ 8547891722519^6243*2000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1054507619 2000000000 8547891722519 20000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8291/2048 : ℝ)) 8291 6243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2114018421/10000000000 : ℝ), (5441072203/10000000000 : ℝ), (1054507619/2000000000 : ℝ)] ![(793583193307/6250000000000 : ℝ), (44563210287067/100000000000000 : ℝ), (8547891722519/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2114018421/10000000000 : ℝ)|^8291 ≤ (793583193307/6250000000000 : ℝ)^6243
        have hw : |(-2114018421/10000000000 : ℝ)|=(2114018421/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5441072203/10000000000 : ℝ)|^8291 ≤ (44563210287067/100000000000000 : ℝ)^6243
        have hw : |(5441072203/10000000000 : ℝ)|=(5441072203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1054507619/2000000000 : ℝ)|^8291 ≤ (8547891722519/20000000000000 : ℝ)^6243
        have hw : |(1054507619/2000000000 : ℝ)|=(1054507619/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1098_box_13 (p : ℝ) (hpa : (4145/1024 : ℝ) ≤ p) (hpb : p ≤ (8291/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5369373833/10000000000 : ℝ)*x 0 + (-552713597/2500000000 : ℝ)*x 1 + (5272538127/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5369373833/10000000000 : ℝ)^8291 ≤ (8757008818793/20000000000000 : ℝ)^6243 := by
    have hnat : (5369373833 : ℕ)^8291*20000000000000^6243 ≤ 8757008818793^6243*10000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5369373833 10000000000 8757008818793 20000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (552713597/2500000000 : ℝ)^8291 ≤ (13475496926261/100000000000000 : ℝ)^6243 := by
    have hnat : (552713597 : ℕ)^8291*100000000000000^6243 ≤ 13475496926261^6243*2500000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      552713597 2500000000 13475496926261 100000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5272538127/10000000000 : ℝ)^8291 ≤ (21369729478541/50000000000000 : ℝ)^6243 := by
    have hnat : (5272538127 : ℕ)^8291*50000000000000^6243 ≤ 21369729478541^6243*10000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5272538127 10000000000 21369729478541 50000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8291/2048 : ℝ)) 8291 6243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5369373833/10000000000 : ℝ), (-552713597/2500000000 : ℝ), (5272538127/10000000000 : ℝ)] ![(8757008818793/20000000000000 : ℝ), (13475496926261/100000000000000 : ℝ), (21369729478541/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5369373833/10000000000 : ℝ)|^8291 ≤ (8757008818793/20000000000000 : ℝ)^6243
        have hw : |(5369373833/10000000000 : ℝ)|=(5369373833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-552713597/2500000000 : ℝ)|^8291 ≤ (13475496926261/100000000000000 : ℝ)^6243
        have hw : |(-552713597/2500000000 : ℝ)|=(552713597/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5272538127/10000000000 : ℝ)|^8291 ≤ (21369729478541/50000000000000 : ℝ)^6243
        have hw : |(5272538127/10000000000 : ℝ)|=(5272538127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1098_box_14 (p : ℝ) (hpa : (4145/1024 : ℝ) ≤ p) (hpb : p ≤ (8291/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2684686917/5000000000 : ℝ)*x 0 + (659067259/1250000000 : ℝ)*x 1 + (-2210854461/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2684686917/5000000000 : ℝ)^8291 ≤ (8757008820959/20000000000000 : ℝ)^6243 := by
    have hnat : (2684686917 : ℕ)^8291*20000000000000^6243 ≤ 8757008820959^6243*5000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2684686917 5000000000 8757008820959 20000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (659067259/1250000000 : ℝ)^8291 ≤ (8547891672999/20000000000000 : ℝ)^6243 := by
    have hnat : (659067259 : ℕ)^8291*20000000000000^6243 ≤ 8547891672999^6243*1250000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      659067259 1250000000 8547891672999 20000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2210854461/10000000000 : ℝ)^8291 ≤ (13475497517171/100000000000000 : ℝ)^6243 := by
    have hnat : (2210854461 : ℕ)^8291*100000000000000^6243 ≤ 13475497517171^6243*10000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2210854461 10000000000 13475497517171 100000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8291/2048 : ℝ)) 8291 6243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2684686917/5000000000 : ℝ), (659067259/1250000000 : ℝ), (-2210854461/10000000000 : ℝ)] ![(8757008820959/20000000000000 : ℝ), (8547891672999/20000000000000 : ℝ), (13475497517171/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2684686917/5000000000 : ℝ)|^8291 ≤ (8757008820959/20000000000000 : ℝ)^6243
        have hw : |(2684686917/5000000000 : ℝ)|=(2684686917/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(659067259/1250000000 : ℝ)|^8291 ≤ (8547891672999/20000000000000 : ℝ)^6243
        have hw : |(659067259/1250000000 : ℝ)|=(659067259/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2210854461/10000000000 : ℝ)|^8291 ≤ (13475497517171/100000000000000 : ℝ)^6243
        have hw : |(-2210854461/10000000000 : ℝ)|=(2210854461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1098_box_15 (p : ℝ) (hpa : (4145/1024 : ℝ) ≤ p) (hpb : p ≤ (8291/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4244317821/10000000000 : ℝ)*x 0 + (4436203781/10000000000 : ℝ)*x 1 + (887240827/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4244317821/10000000000 : ℝ)^8291 ≤ (4005172757893/12500000000000 : ℝ)^6243 := by
    have hnat : (4244317821 : ℕ)^8291*12500000000000^6243 ≤ 4005172757893^6243*10000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4244317821 10000000000 4005172757893 12500000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4436203781/10000000000 : ℝ)^8291 ≤ (4247413394743/12500000000000 : ℝ)^6243 := by
    have hnat : (4436203781 : ℕ)^8291*12500000000000^6243 ≤ 4247413394743^6243*10000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4436203781 10000000000 4247413394743 12500000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (887240827/2000000000 : ℝ)^8291 ≤ (33979310758917/100000000000000 : ℝ)^6243 := by
    have hnat : (887240827 : ℕ)^8291*100000000000000^6243 ≤ 33979310758917^6243*2000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      887240827 2000000000 33979310758917 100000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8291/2048 : ℝ)) 8291 6243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4244317821/10000000000 : ℝ), (4436203781/10000000000 : ℝ), (887240827/2000000000 : ℝ)] ![(4005172757893/12500000000000 : ℝ), (4247413394743/12500000000000 : ℝ), (33979310758917/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4244317821/10000000000 : ℝ)|^8291 ≤ (4005172757893/12500000000000 : ℝ)^6243
        have hw : |(4244317821/10000000000 : ℝ)|=(4244317821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4436203781/10000000000 : ℝ)|^8291 ≤ (4247413394743/12500000000000 : ℝ)^6243
        have hw : |(4436203781/10000000000 : ℝ)|=(4436203781/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(887240827/2000000000 : ℝ)|^8291 ≤ (33979310758917/100000000000000 : ℝ)^6243
        have hw : |(887240827/2000000000 : ℝ)|=(887240827/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1098_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4145/1024 : ℝ) ≤ p) (hpb : p ≤ (8291/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148615943/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7011/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (353/3125 : ℝ)*pair X i i ≤ pair X i h) :
    -(62227/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(11853/20000 : ℝ) ∧ (9959/12500 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (3321/4000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7011/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (353/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7011/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (353/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7011/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (353/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7011/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (353/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7011/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (353/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7011/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (353/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hlower 2 1 (by decide)
  have fm0 := f.main 0
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm0
  have fx01 := abs_le.mp (f.maximal 0 1)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx01
  have fx02 := abs_le.mp (f.maximal 0 2)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx02
  have fm1 := f.main 1
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm1
  have fx10 := abs_le.mp (f.maximal 1 0)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx10
  have fx12 := abs_le.mp (f.maximal 1 2)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx12
  have fm2 := f.main 2
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm2
  have fx20 := abs_le.mp (f.maximal 2 0)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx20
  have fx21 := abs_le.mp (f.maximal 2 1)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx21
  have base65 : ((1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).2]
  have base66 : ((-1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).1]
  have base67 : ((1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).2]
  have base68 : ((-1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).1]
  have base69 : ((1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).2]
  have base70 : ((-1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).1]
  have base71 : ((1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).2]
  have base72 : ((-1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).1]
  have base73 : ((1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).2]
  have base74 : ((-1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).1]
  have base75 : ((1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).2]
  have base76 : ((-1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).1]
  have base77 : ((1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).2]
  have base78 : ((-1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).1]
  have base79 : ((1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).2]
  have base80 : ((-1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).1]
  have base81 : ((1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).2]
  have base82 : ((-1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).1]
  have base83 : ((1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).2]
  have base84 : ((-1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).1]
  have base85 : ((1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).2]
  have base86 : ((-1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).1]
  have base87 : ((1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).2]
  have base88 : ((-1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).1]
  have base89 : ((1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).2]
  have base90 : ((-1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).1]
  have base91 : ((1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).2]
  have base92 : ((-1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).1]
  have base93 : ((1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).2]
  have base94 : ((-1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).1]
  have base95 : ((1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.2]
  have base96 : ((-1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.1]
  have hpowlo : (353/3125 : ℝ) ^ (4145/1024 : ℝ) ≤ (14668297212031837/100000000000000000000 : ℝ) := by
    have hpowers : (353/3125 : ℝ)^4145 ≤ (14668297212031837/100000000000000000000 : ℝ)^1024 := by
      have hnat : (353 : ℕ)^4145*100000000000000000000^1024 ≤ 14668297212031837^1024*3125^4145 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        353 3125 14668297212031837 100000000000000000000 4145 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (353/3125 : ℝ)) (X := (14668297212031837/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4145 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7011/50000 : ℝ) ^ (4145/1024 : ℝ) ≤ (17594761288265837/50000000000000000000 : ℝ) := by
    have hpowers : (7011/50000 : ℝ)^4145 ≤ (17594761288265837/50000000000000000000 : ℝ)^1024 := by
      have hnat : (7011 : ℕ)^4145*50000000000000000000^1024 ≤ 17594761288265837^1024*50000^4145 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7011 50000 17594761288265837 50000000000000000000 4145 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7011/50000 : ℝ)) (X := (17594761288265837/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4145 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014668297212031837/50000000000000000000 : ℝ) ≤ (2000144932957273/2000000000000000 : ℝ) ^ (4145/1024 : ℝ) := by
    have hpowers : (50014668297212031837/50000000000000000000 : ℝ)^1024 ≤ (2000144932957273/2000000000000000 : ℝ)^4145 := by
      have hnat : (50014668297212031837 : ℕ)^1024*2000000000000000^4145 ≤ 2000144932957273^4145*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014668297212031837 50000000000000000000 2000144932957273 2000000000000000 1024 4145 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000144932957273/2000000000000000 : ℝ)) (X := (50014668297212031837/50000000000000000000 : ℝ)) (by norm_num) 4145 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100049857819788563511/100000000000000000000 : ℝ) ≤ (5000615739772739/5000000000000000 : ℝ) ^ (4145/1024 : ℝ) := by
    have hpowers : (100049857819788563511/100000000000000000000 : ℝ)^1024 ≤ (5000615739772739/5000000000000000 : ℝ)^4145 := by
      have hnat : (100049857819788563511 : ℕ)^1024*5000000000000000^4145 ≤ 5000615739772739^4145*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100049857819788563511 100000000000000000000 5000615739772739 5000000000000000 1024 4145 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000615739772739/5000000000000000 : ℝ)) (X := (100049857819788563511/100000000000000000000 : ℝ)) (by norm_num) 4145 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25017594761288265837/25000000000000000000 : ℝ) ≤ (10001738294304591/10000000000000000 : ℝ) ^ (4145/1024 : ℝ) := by
    have hpowers : (25017594761288265837/25000000000000000000 : ℝ)^1024 ≤ (10001738294304591/10000000000000000 : ℝ)^4145 := by
      have hnat : (25017594761288265837 : ℕ)^1024*10000000000000000^4145 ≤ 10001738294304591^4145*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25017594761288265837 25000000000000000000 10001738294304591 10000000000000000 1024 4145 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001738294304591/10000000000000000 : ℝ)) (X := (25017594761288265837/25000000000000000000 : ℝ)) (by norm_num) 4145 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14668297212031837/100000000000000000000 : ℝ) ≤ ((13625262738584875047/13630000000000000000 : ℝ)+2*(506814759113/272600000000000 : ℝ)*(353/3125 : ℝ))^(4145/1024 : ℝ) := by
    rw [show (13625262738584875047/13630000000000000000 : ℝ)+2*(506814759113/272600000000000 : ℝ)*(353/3125 : ℝ)=(2000144932957273/2000000000000000 : ℝ) by norm_num, show 1+2*(14668297212031837/100000000000000000000 : ℝ)=(50014668297212031837/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(17594761288265837/50000000000000000000 : ℝ)+(14668297212031837/100000000000000000000 : ℝ) ≤ ((13625262738584875047/13630000000000000000 : ℝ)+(506814759113/272600000000000 : ℝ)*((7011/50000 : ℝ)+(353/3125 : ℝ)))^(4145/1024 : ℝ) := by
    rw [show (13625262738584875047/13630000000000000000 : ℝ)+(506814759113/272600000000000 : ℝ)*((7011/50000 : ℝ)+(353/3125 : ℝ))=(5000615739772739/5000000000000000 : ℝ) by norm_num, show 1+(17594761288265837/50000000000000000000 : ℝ)+(14668297212031837/100000000000000000000 : ℝ)=(100049857819788563511/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(17594761288265837/50000000000000000000 : ℝ) ≤ ((13625262738584875047/13630000000000000000 : ℝ)+2*(506814759113/272600000000000 : ℝ)*(7011/50000 : ℝ))^(4145/1024 : ℝ) := by
    rw [show (13625262738584875047/13630000000000000000 : ℝ)+2*(506814759113/272600000000000 : ℝ)*(7011/50000 : ℝ)=(10001738294304591/10000000000000000 : ℝ) by norm_num, show 1+2*(17594761288265837/50000000000000000000 : ℝ)=(25017594761288265837/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13625262738584875047/13630000000000000000 : ℝ)*(X 1 0+X 2 0)+(506814759113/272600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4145/1024 : ℝ)) (lo := (353/3125 : ℝ)) (hi := (7011/50000 : ℝ)) (c := (13625262738584875047/13630000000000000000 : ℝ)) (alpha := (506814759113/272600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13625262738584875047/13630000000000000000 : ℝ)*(X 0 1+X 2 1)+(506814759113/272600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4145/1024 : ℝ)) (lo := (353/3125 : ℝ)) (hi := (7011/50000 : ℝ)) (c := (13625262738584875047/13630000000000000000 : ℝ)) (alpha := (506814759113/272600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13625262738584875047/13630000000000000000 : ℝ)*(X 0 2+X 1 2)+(506814759113/272600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4145/1024 : ℝ)) (lo := (353/3125 : ℝ)) (hi := (7011/50000 : ℝ)) (c := (13625262738584875047/13630000000000000000 : ℝ)) (alpha := (506814759113/272600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-205975017/1000000000 : ℝ)*X 0 0+(5376926347/10000000000 : ℝ)*X 0 1+(537692659/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1098_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2647776207/5000000000 : ℝ)*X 1 0+(-1084997061/5000000000 : ℝ)*X 1 1+(1075385299/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1098_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5295552533/10000000000 : ℝ)*X 2 0+(5376926531/10000000000 : ℝ)*X 2 1+(-433998783/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1098_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1119732677/2500000000 : ℝ)*X 0 0+(172761627/400000000 : ℝ)*X 0 1+(4319040653/10000000000 : ℝ)*X 0 2+(1119732677/2500000000 : ℝ)*X 1 0+(172761627/400000000 : ℝ)*X 1 1+(4319040653/10000000000 : ℝ)*X 1 2+(1119732677/2500000000 : ℝ)*X 2 0+(172761627/400000000 : ℝ)*X 2 1+(4319040653/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1098_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2317854561/10000000000 : ℝ)*X 0 0+(1320138731/2500000000 : ℝ)*X 0 1+(5280555399/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1098_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((53637063/100000000 : ℝ)*X 1 0+(-1103885059/5000000000 : ℝ)*X 1 1+(2640277613/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1098_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5363706183/10000000000 : ℝ)*X 2 0+(2640277839/5000000000 : ℝ)*X 2 1+(-275971209/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1098_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4262549271/10000000000 : ℝ)*X 0 0+(2213605289/5000000000 : ℝ)*X 0 1+(885441961/2000000000 : ℝ)*X 0 2+(4262549271/10000000000 : ℝ)*X 1 0+(2213605289/5000000000 : ℝ)*X 1 1+(885441961/2000000000 : ℝ)*X 1 2+(4262549271/10000000000 : ℝ)*X 2 0+(2213605289/5000000000 : ℝ)*X 2 1+(885441961/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1098_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-282991657/1250000000 : ℝ)*X 0 0+(5215098981/10000000000 : ℝ)*X 0 1+(5386530579/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1098_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5288756737/10000000000 : ℝ)*X 1 0+(-433231939/2000000000 : ℝ)*X 1 1+(1077306089/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1098_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((66109461/125000000 : ℝ)*X 2 0+(5386530557/10000000000 : ℝ)*X 2 1+(-2166159353/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1098_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((1125055469/2500000000 : ℝ)*X 0 0+(4308254441/10000000000 : ℝ)*X 0 1+(4308254681/10000000000 : ℝ)*X 0 2+(1125055469/2500000000 : ℝ)*X 1 0+(4308254441/10000000000 : ℝ)*X 1 1+(4308254681/10000000000 : ℝ)*X 1 2+(1125055469/2500000000 : ℝ)*X 2 0+(4308254441/10000000000 : ℝ)*X 2 1+(4308254681/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1098_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-2114018421/10000000000 : ℝ)*X 0 0+(5441072203/10000000000 : ℝ)*X 0 1+(1054507619/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1098_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5369373833/10000000000 : ℝ)*X 1 0+(-552713597/2500000000 : ℝ)*X 1 1+(5272538127/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1098_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((2684686917/5000000000 : ℝ)*X 2 0+(659067259/1250000000 : ℝ)*X 2 1+(-2210854461/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1098_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((4244317821/10000000000 : ℝ)*X 0 0+(4436203781/10000000000 : ℝ)*X 0 1+(887240827/2000000000 : ℝ)*X 0 2+(4244317821/10000000000 : ℝ)*X 1 0+(4436203781/10000000000 : ℝ)*X 1 1+(887240827/2000000000 : ℝ)*X 1 2+(4244317821/10000000000 : ℝ)*X 2 0+(4436203781/10000000000 : ℝ)*X 2 1+(887240827/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1098_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-62227/100000 : ℝ) ≤ (-1060143748329742679575936863/1703750000000000000000000000 : ℝ) := by norm_num
    linear_combination (16072517/100000000000000 : ℝ)*(lower0) + (1126699/1250000000000 : ℝ)*(upper1) + (18749697/10000000000000 : ℝ)*(lower2) + (1941896634164517/50000000000000 : ℝ)*(major0) + (1941896634164517/50000000000000 : ℝ)*(major1) + (1941896634164517/50000000000000 : ℝ)*(major2) + (33634037/800000000000 : ℝ)*(sp3) + (5175017940532691/100000000000000 : ℝ)*(sp4) + (5175017182012021/100000000000000 : ℝ)*(sp5) + (1034915906429063/20000000000000 : ℝ)*(sp6) + (2613304428675177/100000000000000 : ℝ)*(sp7) + (167809153/12500000000000 : ℝ)*(sp12) + (420198779/20000000000000 : ℝ)*(sp13) + (2198754303/500000000000 : ℝ)*(sp14) + (1306654316464901/50000000000000 : ℝ)*(f.failure) + (1293754820751479/25000000000000 : ℝ)*(f.sum) + (9064334049141/6815000000000000000000000000 : ℝ)*base65 + (1403908895491657299/681500000000000000000000000000000 : ℝ)*base67 + (544680195638657299/681500000000000000000000000000000 : ℝ)*base69 + (281812134455842701/681500000000000000000000000000000 : ℝ)*base72 + (27002930173203/851875000000000000000000000 : ℝ)*base74 + (5735062495454342701/681500000000000000000000000000000 : ℝ)*base76 + (5768312330929157299/681500000000000000000000000000000 : ℝ)*base77 + (54402694146249342701/681500000000000000000000000000000 : ℝ)*base80 + (21727879210529/6815000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (11483357/5000000000000000000000 : ℝ)*base90 + (11483357/5000000000000000000000 : ℝ)*base92 + (11483357/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (11853/20000 : ℝ) ≤ (100976776716226755277293741538983/170375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (4475703/25000000000000 : ℝ)*(lower0) + (651/9765625000 : ℝ)*(lower1) + (21616093/25000000000000 : ℝ)*(lower2) + (99918007/100000000000000 : ℝ)*(lower3) + (986809819323837/25000000000000 : ℝ)*(major0) + (986809819323837/25000000000000 : ℝ)*(major1) + (986809819323837/25000000000000 : ℝ)*(major2) + (1043744575824909/20000000000000 : ℝ)*(sp0) + (521871834728649/10000000000000 : ℝ)*(sp1) + (2609357386381899/50000000000000 : ℝ)*(sp2) + (2655999795054441/100000000000000 : ℝ)*(sp3) + (2265919027/50000000000000 : ℝ)*(sp5) + (4053180373/50000000000000 : ℝ)*(sp6) + (22843633/25000000000000 : ℝ)*(sp7) + (2655999886428973/100000000000000 : ℝ)*(f.failure) + (1043744575824909/20000000000000 : ℝ)*(f.sum) + (191301285733/106484375000000000000000000 : ℝ)*base65 + (2821688672451854661/340750000000000000000000000000000 : ℝ)*base68 + (1204220273445395339/340750000000000000000000000000000 : ℝ)*base69 + (2375705253507645339/340750000000000000000000000000000 : ℝ)*base71 + (13021642048677/6815000000000000000000000000 : ℝ)*base73 + (1160506764317604661/340750000000000000000000000000000 : ℝ)*base76 + (1840841634883645339/340750000000000000000000000000000 : ℝ)*base77 + (2438041977749895339/340750000000000000000000000000000 : ℝ)*base79 + (3064393529903/6815000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (75083461/10000000000000000000000 : ℝ)*base90 + (75083461/10000000000000000000000 : ℝ)*base92 + (75083461/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (9959/12500 : ℝ) ≤ (18723618669163305913708761855873/23500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (37747119/50000000000000 : ℝ)*(upper0) + (2799787/20000000000000 : ℝ)*(lower1) + (33116603/25000000000000 : ℝ)*(lower3) + (169966579/100000000000000 : ℝ)*(upper4) + (4415406167354621/100000000000000 : ℝ)*(major0) + (4415406167354621/100000000000000 : ℝ)*(major1) + (4415406167354621/100000000000000 : ℝ)*(major2) + (20982050247/50000000000000 : ℝ)*(sp1) + (169326994237/100000000000000 : ℝ)*(sp2) + (54630295571/50000000000000 : ℝ)*(sp3) + (2916618089302497/50000000000000 : ℝ)*(sp8) + (5833194214504501/100000000000000 : ℝ)*(sp9) + (5833066851610757/100000000000000 : ℝ)*(sp10) + (742727142789917/25000000000000 : ℝ)*(sp11) + (297101783175081/10000000000000 : ℝ)*(f.failure) + (2916618089302497/50000000000000 : ℝ)*(f.sum) + (5773433010027/13630000000000000000000000000 : ℝ)*base66 + (17326045679005692187/1363000000000000000000000000000000 : ℝ)*base67 + (10772038905301692187/1363000000000000000000000000000000 : ℝ)*base69 + (11734401006490692187/1363000000000000000000000000000000 : ℝ)*base71 + (124946475861923/13630000000000000000000000000 : ℝ)*base73 + (4619307044814692187/1363000000000000000000000000000000 : ℝ)*base75 + (8917564242226692187/1363000000000000000000000000000000 : ℝ)*base77 + (22166205362339692187/1363000000000000000000000000000000 : ℝ)*base79 + (112899319815633/13630000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (13083617/1000000000000000000000 : ℝ)*base90 + (13083617/1000000000000000000000 : ℝ)*base92 + (13083617/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-3321/4000 : ℝ) ≤ (-141449972259385442668287437406219/170375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (114547/312500000000 : ℝ)*(lower1) + (24833771/100000000000000 : ℝ)*(lower3) + (71202723/100000000000000 : ℝ)*(lower4) + (161069/400000000000 : ℝ)*(upper5) + (1112528123956959/25000000000000 : ℝ)*(major0) + (1112528123956959/25000000000000 : ℝ)*(major1) + (1112528123956959/25000000000000 : ℝ)*(major2) + (4469096931/50000000000000 : ℝ)*(sp4) + (63338476217/50000000000000 : ℝ)*(sp6) + (31348223577/50000000000000 : ℝ)*(sp7) + (741689929054503/12500000000000 : ℝ)*(sp12) + (5933528370629887/100000000000000 : ℝ)*(sp13) + (1483350423419363/25000000000000 : ℝ)*(sp14) + (748577041783409/25000000000000 : ℝ)*(sp15) + (2994370863580791/100000000000000 : ℝ)*(f.failure) + (5933528370629887/100000000000000 : ℝ)*(f.sum) + (4971479104737/3407500000000000000000000000 : ℝ)*base65 + (5557898918603452073/340750000000000000000000000000000 : ℝ)*base67 + (1635686244016547927/340750000000000000000000000000000 : ℝ)*base70 + (2419997363278702073/340750000000000000000000000000000 : ℝ)*base71 + (23347345033277/3407500000000000000000000000 : ℝ)*base73 + (3588220010379797927/340750000000000000000000000000000 : ℝ)*base76 + (3489358259179452073/340750000000000000000000000000000 : ℝ)*base77 + (6225886328786452073/340750000000000000000000000000000 : ℝ)*base79 + (94163454899427/851875000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (11150913/10000000000000000000000 : ℝ)*base89 + (11150913/10000000000000000000000 : ℝ)*base91 + (11150913/10000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1098_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4145/1024 : ℝ) ≤ p) (hpb : p ≤ (8291/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148615943/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7011/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (353/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62227/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(11853/20000 : ℝ) else (9959/12500 : ℝ) ≤ X j i ∧ X j i ≤ (3321/4000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1098_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1098_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4145/1024 : ℝ) ≤ p) (hpb : p ≤ (8291/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148615943/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7011/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2259/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62227/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(11853/20000 : ℝ) else (9959/12500 : ℝ) ≤ X j i ∧ X j i ≤ (3321/4000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1098_s9 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1098_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4145/1024 : ℝ) ≤ p) (hpb : p ≤ (8291/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148615943/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7011/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2259/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62227/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(11853/20000 : ℝ) else (9959/12500 : ℝ) ≤ X j i ∧ X j i ≤ (3321/4000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1098_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
