-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1756_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:23:51.548988+00:00
-- url     : https://prove2.me/submissions/0453efa7-975a-4abe-930c-79fd6bcdf414

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
theorem support_rectangle_w1756_s0_0 (p : ℝ) (hpa : (5855/1024 : ℝ) ≤ p) (hpb : p ≤ (5871/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1149007037/10000000000 : ℝ)*x 0 + (5612341557/10000000000 : ℝ)*x 1 + (4986661137/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1149007037/10000000000 : ℝ)^5871 ≤ (7274481493557/100000000000000 : ℝ)^4847 := by
    have hnat : (1149007037 : ℕ)^5871*100000000000000^4847 ≤ 7274481493557^4847*10000000000^5871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1149007037 10000000000 7274481493557 100000000000000 5871 4847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5612341557/10000000000 : ℝ)^5871 ≤ (248380273007/500000000000 : ℝ)^4847 := by
    have hnat : (5612341557 : ℕ)^5871*500000000000^4847 ≤ 248380273007^4847*10000000000^5871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5612341557 10000000000 248380273007 500000000000 5871 4847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4986661137/10000000000 : ℝ)^5871 ≤ (10762365973007/25000000000000 : ℝ)^4847 := by
    have hnat : (4986661137 : ℕ)^5871*25000000000000^4847 ≤ 10762365973007^4847*10000000000^5871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4986661137 10000000000 10762365973007 25000000000000 5871 4847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5871/1024 : ℝ)) 5871 4847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1149007037/10000000000 : ℝ), (5612341557/10000000000 : ℝ), (4986661137/10000000000 : ℝ)] ![(7274481493557/100000000000000 : ℝ), (248380273007/500000000000 : ℝ), (10762365973007/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1149007037/10000000000 : ℝ)|^5871 ≤ (7274481493557/100000000000000 : ℝ)^4847
        have hw : |(-1149007037/10000000000 : ℝ)|=(1149007037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5612341557/10000000000 : ℝ)|^5871 ≤ (248380273007/500000000000 : ℝ)^4847
        have hw : |(5612341557/10000000000 : ℝ)|=(5612341557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4986661137/10000000000 : ℝ)|^5871 ≤ (10762365973007/25000000000000 : ℝ)^4847
        have hw : |(4986661137/10000000000 : ℝ)|=(4986661137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1756_s0_1 (p : ℝ) (hpa : (5855/1024 : ℝ) ≤ p) (hpb : p ≤ (5871/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2682450423/5000000000 : ℝ)*x 0 + (-741856179/5000000000 : ℝ)*x 1 + (4986661739/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2682450423/5000000000 : ℝ)^5871 ≤ (47035702352157/100000000000000 : ℝ)^4847 := by
    have hnat : (2682450423 : ℕ)^5871*100000000000000^4847 ≤ 47035702352157^4847*5000000000^5871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2682450423 5000000000 47035702352157 100000000000000 5871 4847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (741856179/5000000000 : ℝ)^5871 ≤ (1982965488087/20000000000000 : ℝ)^4847 := by
    have hnat : (741856179 : ℕ)^5871*20000000000000^4847 ≤ 1982965488087^4847*5000000000^5871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      741856179 5000000000 1982965488087 20000000000000 5871 4847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4986661739/10000000000 : ℝ)^5871 ≤ (21524735093497/50000000000000 : ℝ)^4847 := by
    have hnat : (4986661739 : ℕ)^5871*50000000000000^4847 ≤ 21524735093497^4847*10000000000^5871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4986661739 10000000000 21524735093497 50000000000000 5871 4847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5871/1024 : ℝ)) 5871 4847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2682450423/5000000000 : ℝ), (-741856179/5000000000 : ℝ), (4986661739/10000000000 : ℝ)] ![(47035702352157/100000000000000 : ℝ), (1982965488087/20000000000000 : ℝ), (21524735093497/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2682450423/5000000000 : ℝ)|^5871 ≤ (47035702352157/100000000000000 : ℝ)^4847
        have hw : |(2682450423/5000000000 : ℝ)|=(2682450423/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-741856179/5000000000 : ℝ)|^5871 ≤ (1982965488087/20000000000000 : ℝ)^4847
        have hw : |(-741856179/5000000000 : ℝ)|=(741856179/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4986661739/10000000000 : ℝ)|^5871 ≤ (21524735093497/50000000000000 : ℝ)^4847
        have hw : |(4986661739/10000000000 : ℝ)|=(4986661739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1756_s0_2 (p : ℝ) (hpa : (5855/1024 : ℝ) ≤ p) (hpb : p ≤ (5871/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1072980743/2000000000 : ℝ)*x 0 + (2493330081/5000000000 : ℝ)*x 1 + (-1483710631/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1072980743/2000000000 : ℝ)^5871 ≤ (47035732819569/100000000000000 : ℝ)^4847 := by
    have hnat : (1072980743 : ℕ)^5871*100000000000000^4847 ≤ 47035732819569^4847*2000000000^5871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1072980743 2000000000 47035732819569 100000000000000 5871 4847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2493330081/5000000000 : ℝ)^5871 ≤ (43049453696691/100000000000000 : ℝ)^4847 := by
    have hnat : (2493330081 : ℕ)^5871*100000000000000^4847 ≤ 43049453696691^4847*5000000000^5871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2493330081 5000000000 43049453696691 100000000000000 5871 4847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1483710631/10000000000 : ℝ)^5871 ≤ (1982962692347/20000000000000 : ℝ)^4847 := by
    have hnat : (1483710631 : ℕ)^5871*20000000000000^4847 ≤ 1982962692347^4847*10000000000^5871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1483710631 10000000000 1982962692347 20000000000000 5871 4847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5871/1024 : ℝ)) 5871 4847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1072980743/2000000000 : ℝ), (2493330081/5000000000 : ℝ), (-1483710631/10000000000 : ℝ)] ![(47035732819569/100000000000000 : ℝ), (43049453696691/100000000000000 : ℝ), (1982962692347/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1072980743/2000000000 : ℝ)|^5871 ≤ (47035732819569/100000000000000 : ℝ)^4847
        have hw : |(1072980743/2000000000 : ℝ)|=(1072980743/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2493330081/5000000000 : ℝ)|^5871 ≤ (43049453696691/100000000000000 : ℝ)^4847
        have hw : |(2493330081/5000000000 : ℝ)|=(2493330081/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1483710631/10000000000 : ℝ)|^5871 ≤ (1982962692347/20000000000000 : ℝ)^4847
        have hw : |(-1483710631/10000000000 : ℝ)|=(1483710631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1756_s0_3 (p : ℝ) (hpa : (5855/1024 : ℝ) ≤ p) (hpb : p ≤ (5871/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1984380349/5000000000 : ℝ)*x 0 + (93415551/312500000 : ℝ)*x 1 + (2547713651/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1984380349/5000000000 : ℝ)^5871 ≤ (32648622624081/100000000000000 : ℝ)^4847 := by
    have hnat : (1984380349 : ℕ)^5871*100000000000000^4847 ≤ 32648622624081^4847*5000000000^5871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1984380349 5000000000 32648622624081 100000000000000 5871 4847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (93415551/312500000 : ℝ)^5871 ≤ (5790491685897/25000000000000 : ℝ)^4847 := by
    have hnat : (93415551 : ℕ)^5871*25000000000000^4847 ≤ 5790491685897^4847*312500000^5871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      93415551 312500000 5790491685897 25000000000000 5871 4847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2547713651/5000000000 : ℝ)^5871 ≤ (22094705310959/50000000000000 : ℝ)^4847 := by
    have hnat : (2547713651 : ℕ)^5871*50000000000000^4847 ≤ 22094705310959^4847*5000000000^5871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2547713651 5000000000 22094705310959 50000000000000 5871 4847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5871/1024 : ℝ)) 5871 4847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1984380349/5000000000 : ℝ), (93415551/312500000 : ℝ), (2547713651/5000000000 : ℝ)] ![(32648622624081/100000000000000 : ℝ), (5790491685897/25000000000000 : ℝ), (22094705310959/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1984380349/5000000000 : ℝ)|^5871 ≤ (32648622624081/100000000000000 : ℝ)^4847
        have hw : |(1984380349/5000000000 : ℝ)|=(1984380349/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(93415551/312500000 : ℝ)|^5871 ≤ (5790491685897/25000000000000 : ℝ)^4847
        have hw : |(93415551/312500000 : ℝ)|=(93415551/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2547713651/5000000000 : ℝ)|^5871 ≤ (22094705310959/50000000000000 : ℝ)^4847
        have hw : |(2547713651/5000000000 : ℝ)|=(2547713651/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1756_s0_4 (p : ℝ) (hpa : (5855/1024 : ℝ) ≤ p) (hpb : p ≤ (5871/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-230050293/2000000000 : ℝ)*x 0 + (5002449389/10000000000 : ℝ)*x 1 + (5596042317/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (230050293/2000000000 : ℝ)^5871 ≤ (1456805131357/20000000000000 : ℝ)^4847 := by
    have hnat : (230050293 : ℕ)^5871*20000000000000^4847 ≤ 1456805131357^4847*2000000000^5871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      230050293 2000000000 1456805131357 20000000000000 5871 4847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5002449389/10000000000 : ℝ)^5871 ≤ (864292259009/2000000000000 : ℝ)^4847 := by
    have hnat : (5002449389 : ℕ)^5871*2000000000000^4847 ≤ 864292259009^4847*10000000000^5871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5002449389 10000000000 864292259009 2000000000000 5871 4847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5596042317/10000000000 : ℝ)^5871 ≤ (49501361375587/100000000000000 : ℝ)^4847 := by
    have hnat : (5596042317 : ℕ)^5871*100000000000000^4847 ≤ 49501361375587^4847*10000000000^5871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5596042317 10000000000 49501361375587 100000000000000 5871 4847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5871/1024 : ℝ)) 5871 4847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-230050293/2000000000 : ℝ), (5002449389/10000000000 : ℝ), (5596042317/10000000000 : ℝ)] ![(1456805131357/20000000000000 : ℝ), (864292259009/2000000000000 : ℝ), (49501361375587/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-230050293/2000000000 : ℝ)|^5871 ≤ (1456805131357/20000000000000 : ℝ)^4847
        have hw : |(-230050293/2000000000 : ℝ)|=(230050293/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5002449389/10000000000 : ℝ)|^5871 ≤ (864292259009/2000000000000 : ℝ)^4847
        have hw : |(5002449389/10000000000 : ℝ)|=(5002449389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5596042317/10000000000 : ℝ)|^5871 ≤ (49501361375587/100000000000000 : ℝ)^4847
        have hw : |(5596042317/10000000000 : ℝ)|=(5596042317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1756_s0_5 (p : ℝ) (hpa : (5855/1024 : ℝ) ≤ p) (hpb : p ≤ (5871/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1299605289/2500000000 : ℝ)*x 0 + (-437164869/5000000000 : ℝ)*x 1 + (1399010589/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1299605289/2500000000 : ℝ)^5871 ≤ (22636805294869/50000000000000 : ℝ)^4847 := by
    have hnat : (1299605289 : ℕ)^5871*50000000000000^4847 ≤ 22636805294869^4847*2500000000^5871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1299605289 2500000000 22636805294869 50000000000000 5871 4847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (437164869/5000000000 : ℝ)^5871 ≤ (326564225413/6250000000000 : ℝ)^4847 := by
    have hnat : (437164869 : ℕ)^5871*6250000000000^4847 ≤ 326564225413^4847*5000000000^5871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      437164869 5000000000 326564225413 6250000000000 5871 4847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1399010589/2500000000 : ℝ)^5871 ≤ (9900272358691/20000000000000 : ℝ)^4847 := by
    have hnat : (1399010589 : ℕ)^5871*20000000000000^4847 ≤ 9900272358691^4847*2500000000^5871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1399010589 2500000000 9900272358691 20000000000000 5871 4847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5871/1024 : ℝ)) 5871 4847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1299605289/2500000000 : ℝ), (-437164869/5000000000 : ℝ), (1399010589/2500000000 : ℝ)] ![(22636805294869/50000000000000 : ℝ), (326564225413/6250000000000 : ℝ), (9900272358691/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1299605289/2500000000 : ℝ)|^5871 ≤ (22636805294869/50000000000000 : ℝ)^4847
        have hw : |(1299605289/2500000000 : ℝ)|=(1299605289/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-437164869/5000000000 : ℝ)|^5871 ≤ (326564225413/6250000000000 : ℝ)^4847
        have hw : |(-437164869/5000000000 : ℝ)|=(437164869/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1399010589/2500000000 : ℝ)|^5871 ≤ (9900272358691/20000000000000 : ℝ)^4847
        have hw : |(1399010589/2500000000 : ℝ)|=(1399010589/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1756_s0_6 (p : ℝ) (hpa : (5855/1024 : ℝ) ≤ p) (hpb : p ≤ (5871/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (103968411/200000000 : ℝ)*x 0 + (5596042499/10000000000 : ℝ)*x 1 + (-874330409/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (103968411/200000000 : ℝ)^5871 ≤ (45273604197023/100000000000000 : ℝ)^4847 := by
    have hnat : (103968411 : ℕ)^5871*100000000000000^4847 ≤ 45273604197023^4847*200000000^5871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      103968411 200000000 45273604197023 100000000000000 5871 4847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5596042499/10000000000 : ℝ)^5871 ≤ (49501363325641/100000000000000 : ℝ)^4847 := by
    have hnat : (5596042499 : ℕ)^5871*100000000000000^4847 ≤ 49501363325641^4847*10000000000^5871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5596042499 10000000000 49501363325641 100000000000000 5871 4847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (874330409/10000000000 : ℝ)^5871 ≤ (1045006492737/20000000000000 : ℝ)^4847 := by
    have hnat : (874330409 : ℕ)^5871*20000000000000^4847 ≤ 1045006492737^4847*10000000000^5871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      874330409 10000000000 1045006492737 20000000000000 5871 4847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5871/1024 : ℝ)) 5871 4847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(103968411/200000000 : ℝ), (5596042499/10000000000 : ℝ), (-874330409/10000000000 : ℝ)] ![(45273604197023/100000000000000 : ℝ), (49501363325641/100000000000000 : ℝ), (1045006492737/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(103968411/200000000 : ℝ)|^5871 ≤ (45273604197023/100000000000000 : ℝ)^4847
        have hw : |(103968411/200000000 : ℝ)|=(103968411/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5596042499/10000000000 : ℝ)|^5871 ≤ (49501363325641/100000000000000 : ℝ)^4847
        have hw : |(5596042499/10000000000 : ℝ)|=(5596042499/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-874330409/10000000000 : ℝ)|^5871 ≤ (1045006492737/20000000000000 : ℝ)^4847
        have hw : |(-874330409/10000000000 : ℝ)|=(874330409/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1756_s0_7 (p : ℝ) (hpa : (5855/1024 : ℝ) ≤ p) (hpb : p ≤ (5871/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (79459019/200000000 : ℝ)*x 0 + (5042279299/10000000000 : ℝ)*x 1 + (152208161/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (79459019/200000000 : ℝ)^5871 ≤ (32690380420543/100000000000000 : ℝ)^4847 := by
    have hnat : (79459019 : ℕ)^5871*100000000000000^4847 ≤ 32690380420543^4847*200000000^5871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      79459019 200000000 32690380420543 100000000000000 5871 4847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5042279299/10000000000 : ℝ)^5871 ≤ (21815866305279/50000000000000 : ℝ)^4847 := by
    have hnat : (5042279299 : ℕ)^5871*50000000000000^4847 ≤ 21815866305279^4847*10000000000^5871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5042279299 10000000000 21815866305279 50000000000000 5871 4847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (152208161/500000000 : ℝ)^5871 ≤ (23677886949003/100000000000000 : ℝ)^4847 := by
    have hnat : (152208161 : ℕ)^5871*100000000000000^4847 ≤ 23677886949003^4847*500000000^5871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      152208161 500000000 23677886949003 100000000000000 5871 4847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5871/1024 : ℝ)) 5871 4847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(79459019/200000000 : ℝ), (5042279299/10000000000 : ℝ), (152208161/500000000 : ℝ)] ![(32690380420543/100000000000000 : ℝ), (21815866305279/50000000000000 : ℝ), (23677886949003/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(79459019/200000000 : ℝ)|^5871 ≤ (32690380420543/100000000000000 : ℝ)^4847
        have hw : |(79459019/200000000 : ℝ)|=(79459019/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5042279299/10000000000 : ℝ)|^5871 ≤ (21815866305279/50000000000000 : ℝ)^4847
        have hw : |(5042279299/10000000000 : ℝ)|=(5042279299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(152208161/500000000 : ℝ)|^5871 ≤ (23677886949003/100000000000000 : ℝ)^4847
        have hw : |(152208161/500000000 : ℝ)|=(152208161/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1756_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5855/1024 : ℝ) ≤ p) (hpb : p ≤ (5871/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (43661367/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (6957/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (20503/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2/5 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (0 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2/5 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (0 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2/5 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (0 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2/5 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (0 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2/5 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (0 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2/5 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (0 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base24 : ((-1 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 2).1]
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
  have hpowlo : (0 : ℝ) ^ (5855/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^5855 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^5855*1^1024 ≤ 0^1024*1^5855 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 5855 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 5855 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (5855/1024 : ℝ) ≤ (265240106141679071/50000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^5855 ≤ (265240106141679071/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^5855*50000000000000000000^1024 ≤ 265240106141679071^1024*5^5855 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 265240106141679071 50000000000000000000 5855 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (265240106141679071/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5855 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (5855/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^5855 := by
      have hnat : (1 : ℕ)^1024*1^5855 ≤ 1^5855*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 5855 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 5855 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50265240106141679071/50000000000000000000 : ℝ) ≤ (10009257501848609/10000000000000000 : ℝ) ^ (5855/1024 : ℝ) := by
    have hpowers : (50265240106141679071/50000000000000000000 : ℝ)^1024 ≤ (10009257501848609/10000000000000000 : ℝ)^5855 := by
      have hnat : (50265240106141679071 : ℕ)^1024*10000000000000000^5855 ≤ 10009257501848609^5855*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50265240106141679071 50000000000000000000 10009257501848609 10000000000000000 1024 5855 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10009257501848609/10000000000000000 : ℝ)) (X := (50265240106141679071/50000000000000000000 : ℝ)) (by norm_num) 5855 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25265240106141679071/25000000000000000000 : ℝ) ≤ (5009257501848609/5000000000000000 : ℝ) ^ (5855/1024 : ℝ) := by
    have hpowers : (25265240106141679071/25000000000000000000 : ℝ)^1024 ≤ (5009257501848609/5000000000000000 : ℝ)^5855 := by
      have hnat : (25265240106141679071 : ℕ)^1024*5000000000000000^5855 ≤ 5009257501848609^5855*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25265240106141679071 25000000000000000000 5009257501848609 5000000000000000 1024 5855 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5009257501848609/5000000000000000 : ℝ)) (X := (25265240106141679071/25000000000000000000 : ℝ)) (by norm_num) 5855 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(9257501848609/4000000000000000 : ℝ)*(0 : ℝ))^(5855/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(9257501848609/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(265240106141679071/50000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(9257501848609/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(5855/1024 : ℝ) := by
    rw [show (1 : ℝ)+(9257501848609/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10009257501848609/10000000000000000 : ℝ) by norm_num, show 1+(265240106141679071/50000000000000000000 : ℝ)+(0 : ℝ)=(50265240106141679071/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(265240106141679071/50000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(9257501848609/4000000000000000 : ℝ)*(2/5 : ℝ))^(5855/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(9257501848609/4000000000000000 : ℝ)*(2/5 : ℝ)=(5009257501848609/5000000000000000 : ℝ) by norm_num, show 1+2*(265240106141679071/50000000000000000000 : ℝ)=(25265240106141679071/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(9257501848609/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5855/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (9257501848609/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(9257501848609/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5855/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (9257501848609/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(9257501848609/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5855/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (9257501848609/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1149007037/10000000000 : ℝ)*X 0 0+(5612341557/10000000000 : ℝ)*X 0 1+(4986661137/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1756_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2682450423/5000000000 : ℝ)*X 1 0+(-741856179/5000000000 : ℝ)*X 1 1+(4986661739/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1756_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1072980743/2000000000 : ℝ)*X 2 0+(2493330081/5000000000 : ℝ)*X 2 1+(-1483710631/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1756_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1984380349/5000000000 : ℝ)*X 0 0+(93415551/312500000 : ℝ)*X 0 1+(2547713651/5000000000 : ℝ)*X 0 2+(1984380349/5000000000 : ℝ)*X 1 0+(93415551/312500000 : ℝ)*X 1 1+(2547713651/5000000000 : ℝ)*X 1 2+(1984380349/5000000000 : ℝ)*X 2 0+(93415551/312500000 : ℝ)*X 2 1+(2547713651/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1756_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-230050293/2000000000 : ℝ)*X 0 0+(5002449389/10000000000 : ℝ)*X 0 1+(5596042317/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1756_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1299605289/2500000000 : ℝ)*X 1 0+(-437164869/5000000000 : ℝ)*X 1 1+(1399010589/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1756_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((103968411/200000000 : ℝ)*X 2 0+(5596042499/10000000000 : ℝ)*X 2 1+(-874330409/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1756_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((79459019/200000000 : ℝ)*X 0 0+(5042279299/10000000000 : ℝ)*X 0 1+(152208161/500000000 : ℝ)*X 0 2+(79459019/200000000 : ℝ)*X 1 0+(5042279299/10000000000 : ℝ)*X 1 1+(152208161/500000000 : ℝ)*X 1 2+(79459019/200000000 : ℝ)*X 2 0+(5042279299/10000000000 : ℝ)*X 2 1+(152208161/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1756_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (427499433302212905490023/40000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (850306953/50000000000000 : ℝ)*(base19) + (2308851409/100000000000000 : ℝ)*(base23) + (17216923/25000000000000 : ℝ)*(base24) + (952859/1000000000000 : ℝ)*(upper4) + (60711971/10000000000000 : ℝ)*(upper5) + (1036546537386451/100000000000000 : ℝ)*(major0) + (1036546537386451/100000000000000 : ℝ)*(major1) + (1036546537386451/100000000000000 : ℝ)*(major2) + (319653076660659/20000000000000 : ℝ)*(sp0) + (399569813112011/25000000000000 : ℝ)*(sp1) + (1598278575342849/100000000000000 : ℝ)*(sp2) + (14837775145403/3125000000000 : ℝ)*(sp3) + (3113951731/20000000000000 : ℝ)*(sp4) + (740202131/25000000000000 : ℝ)*(sp7) + (474811765461421/100000000000000 : ℝ)*(f.failure) + (31965619061239/2000000000000 : ℝ)*(f.sum) + (228041386196659/200000000000000000000000000000 : ℝ)*base65 + (924692306596659/400000000000000000000000000000 : ℝ)*base67 + (387022360996659/400000000000000000000000000000 : ℝ)*base69 + (249174156996659/400000000000000000000000000000 : ℝ)*base71 + (962672090596659/200000000000000000000000000000 : ℝ)*base73 + (2633966974596659/400000000000000000000000000000 : ℝ)*base75 + (580318632596659/400000000000000000000000000000 : ℝ)*base77 + (496963464603341/400000000000000000000000000000 : ℝ)*base80 + (7278699196659/200000000000000000000000000000 : ℝ)*base81 + (6622507/2000000000000000000000 : ℝ)*base89 + (6622507/2000000000000000000000 : ℝ)*base91 + (6622507/2000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (886137740485086262486851/200000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1298773039/100000000000000 : ℝ)*(base19) + (1173578963/100000000000000 : ℝ)*(base23) + (58933187/100000000000000 : ℝ)*(upper2) + (111381961/50000000000000 : ℝ)*(upper3) + (96307993/50000000000000 : ℝ)*(upper5) + (1092563178130229/100000000000000 : ℝ)*(major0) + (1092563178130229/100000000000000 : ℝ)*(major1) + (1092563178130229/100000000000000 : ℝ)*(major2) + (1459598349/25000000000000 : ℝ)*(sp1) + (2260680971/50000000000000 : ℝ)*(sp2) + (84232742611019/5000000000000 : ℝ)*(sp4) + (336929543010789/20000000000000 : ℝ)*(sp5) + (842324578639737/50000000000000 : ℝ)*(sp6) + (100094271270089/20000000000000 : ℝ)*(sp7) + (100094271270089/20000000000000 : ℝ)*(f.failure) + (84232742611019/5000000000000 : ℝ)*(f.sum) + (1039564434501461/200000000000000000000000000000 : ℝ)*base65 + (1375786705498539/400000000000000000000000000000 : ℝ)*base68 + (1923346300501461/400000000000000000000000000000 : ℝ)*base69 + (380669170101461/400000000000000000000000000000 : ℝ)*base71 + (103759130898539/200000000000000000000000000000 : ℝ)*base74 + (1035926458901461/400000000000000000000000000000 : ℝ)*base75 + (3428776452501461/400000000000000000000000000000 : ℝ)*base77 + (2362464370501461/400000000000000000000000000000 : ℝ)*base79 + (653987118101461/200000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (4048337/400000000000000000000 : ℝ)*base90 + (4048337/400000000000000000000 : ℝ)*base92 + (4048337/400000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1756_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5855/1024 : ℝ) ≤ p) (hpb : p ≤ (5871/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (43661367/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (6957/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (20503/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1756_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1756_s1_0 (p : ℝ) (hpa : (5855/1024 : ℝ) ≤ p) (hpb : p ≤ (5871/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-237744247/2000000000 : ℝ)*x 0 + (5491601337/10000000000 : ℝ)*x 1 + (5080754393/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (237744247/2000000000 : ℝ)^5871 ≤ (1895034355649/25000000000000 : ℝ)^4847 := by
    have hnat : (237744247 : ℕ)^5871*25000000000000^4847 ≤ 1895034355649^4847*2000000000^5871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      237744247 2000000000 1895034355649 25000000000000 5871 4847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5491601337/10000000000 : ℝ)^5871 ≤ (24192268518517/50000000000000 : ℝ)^4847 := by
    have hnat : (5491601337 : ℕ)^5871*50000000000000^4847 ≤ 24192268518517^4847*10000000000^5871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5491601337 10000000000 24192268518517 50000000000000 5871 4847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5080754393/10000000000 : ℝ)^5871 ≤ (4403532551657/10000000000000 : ℝ)^4847 := by
    have hnat : (5080754393 : ℕ)^5871*10000000000000^4847 ≤ 4403532551657^4847*10000000000^5871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5080754393 10000000000 4403532551657 10000000000000 5871 4847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5871/1024 : ℝ)) 5871 4847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-237744247/2000000000 : ℝ), (5491601337/10000000000 : ℝ), (5080754393/10000000000 : ℝ)] ![(1895034355649/25000000000000 : ℝ), (24192268518517/50000000000000 : ℝ), (4403532551657/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-237744247/2000000000 : ℝ)|^5871 ≤ (1895034355649/25000000000000 : ℝ)^4847
        have hw : |(-237744247/2000000000 : ℝ)|=(237744247/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5491601337/10000000000 : ℝ)|^5871 ≤ (24192268518517/50000000000000 : ℝ)^4847
        have hw : |(5491601337/10000000000 : ℝ)|=(5491601337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5080754393/10000000000 : ℝ)|^5871 ≤ (4403532551657/10000000000000 : ℝ)^4847
        have hw : |(5080754393/10000000000 : ℝ)|=(5080754393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1756_s1_1 (p : ℝ) (hpa : (5855/1024 : ℝ) ≤ p) (hpb : p ≤ (5871/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2666406733/5000000000 : ℝ)*x 0 + (-1403522623/10000000000 : ℝ)*x 1 + (5080753893/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2666406733/5000000000 : ℝ)^5871 ≤ (11673791329091/25000000000000 : ℝ)^4847 := by
    have hnat : (2666406733 : ℕ)^5871*25000000000000^4847 ≤ 11673791329091^4847*5000000000^5871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2666406733 5000000000 11673791329091 25000000000000 5871 4847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1403522623/10000000000 : ℝ)^5871 ≤ (144836162513/1562500000000 : ℝ)^4847 := by
    have hnat : (1403522623 : ℕ)^5871*1562500000000^4847 ≤ 144836162513^4847*10000000000^5871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1403522623 10000000000 144836162513 1562500000000 5871 4847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5080753893/10000000000 : ℝ)^5871 ≤ (44035320267503/100000000000000 : ℝ)^4847 := by
    have hnat : (5080753893 : ℕ)^5871*100000000000000^4847 ≤ 44035320267503^4847*10000000000^5871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5080753893 10000000000 44035320267503 100000000000000 5871 4847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5871/1024 : ℝ)) 5871 4847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2666406733/5000000000 : ℝ), (-1403522623/10000000000 : ℝ), (5080753893/10000000000 : ℝ)] ![(11673791329091/25000000000000 : ℝ), (144836162513/1562500000000 : ℝ), (44035320267503/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2666406733/5000000000 : ℝ)|^5871 ≤ (11673791329091/25000000000000 : ℝ)^4847
        have hw : |(2666406733/5000000000 : ℝ)|=(2666406733/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1403522623/10000000000 : ℝ)|^5871 ≤ (144836162513/1562500000000 : ℝ)^4847
        have hw : |(-1403522623/10000000000 : ℝ)|=(1403522623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5080753893/10000000000 : ℝ)|^5871 ≤ (44035320267503/100000000000000 : ℝ)^4847
        have hw : |(5080753893/10000000000 : ℝ)|=(5080753893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1756_s1_2 (p : ℝ) (hpa : (5855/1024 : ℝ) ≤ p) (hpb : p ≤ (5871/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5332811737/10000000000 : ℝ)*x 0 + (40646041/80000000 : ℝ)*x 1 + (-1403523299/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5332811737/10000000000 : ℝ)^5871 ≤ (9339029395693/20000000000000 : ℝ)^4847 := by
    have hnat : (5332811737 : ℕ)^5871*20000000000000^4847 ≤ 9339029395693^4847*10000000000^5871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5332811737 10000000000 9339029395693 20000000000000 5871 4847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (40646041/80000000 : ℝ)^5871 ≤ (44035333201203/100000000000000 : ℝ)^4847 := by
    have hnat : (40646041 : ℕ)^5871*100000000000000^4847 ≤ 44035333201203^4847*80000000^5871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      40646041 80000000 44035333201203 100000000000000 5871 4847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1403523299/10000000000 : ℝ)^5871 ≤ (4634759904333/50000000000000 : ℝ)^4847 := by
    have hnat : (1403523299 : ℕ)^5871*50000000000000^4847 ≤ 4634759904333^4847*10000000000^5871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1403523299 10000000000 4634759904333 50000000000000 5871 4847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5871/1024 : ℝ)) 5871 4847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5332811737/10000000000 : ℝ), (40646041/80000000 : ℝ), (-1403523299/10000000000 : ℝ)] ![(9339029395693/20000000000000 : ℝ), (44035333201203/100000000000000 : ℝ), (4634759904333/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5332811737/10000000000 : ℝ)|^5871 ≤ (9339029395693/20000000000000 : ℝ)^4847
        have hw : |(5332811737/10000000000 : ℝ)|=(5332811737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(40646041/80000000 : ℝ)|^5871 ≤ (44035333201203/100000000000000 : ℝ)^4847
        have hw : |(40646041/80000000 : ℝ)|=(40646041/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1403523299/10000000000 : ℝ)|^5871 ≤ (4634759904333/50000000000000 : ℝ)^4847
        have hw : |(-1403523299/10000000000 : ℝ)|=(1403523299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1756_s1_3 (p : ℝ) (hpa : (5855/1024 : ℝ) ≤ p) (hpb : p ≤ (5871/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1001983407/2500000000 : ℝ)*x 0 + (1674008549/5000000000 : ℝ)*x 1 + (2365492789/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1001983407/2500000000 : ℝ)^5871 ≤ (33039361362139/100000000000000 : ℝ)^4847 := by
    have hnat : (1001983407 : ℕ)^5871*100000000000000^4847 ≤ 33039361362139^4847*2500000000^5871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1001983407 2500000000 33039361362139 100000000000000 5871 4847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1674008549/5000000000 : ℝ)^5871 ≤ (26570031934911/100000000000000 : ℝ)^4847 := by
    have hnat : (1674008549 : ℕ)^5871*100000000000000^4847 ≤ 26570031934911^4847*5000000000^5871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1674008549 5000000000 26570031934911 100000000000000 5871 4847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2365492789/5000000000 : ℝ)^5871 ≤ (40390606691881/100000000000000 : ℝ)^4847 := by
    have hnat : (2365492789 : ℕ)^5871*100000000000000^4847 ≤ 40390606691881^4847*5000000000^5871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2365492789 5000000000 40390606691881 100000000000000 5871 4847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5871/1024 : ℝ)) 5871 4847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1001983407/2500000000 : ℝ), (1674008549/5000000000 : ℝ), (2365492789/5000000000 : ℝ)] ![(33039361362139/100000000000000 : ℝ), (26570031934911/100000000000000 : ℝ), (40390606691881/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1001983407/2500000000 : ℝ)|^5871 ≤ (33039361362139/100000000000000 : ℝ)^4847
        have hw : |(1001983407/2500000000 : ℝ)|=(1001983407/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1674008549/5000000000 : ℝ)|^5871 ≤ (26570031934911/100000000000000 : ℝ)^4847
        have hw : |(1674008549/5000000000 : ℝ)|=(1674008549/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2365492789/5000000000 : ℝ)|^5871 ≤ (40390606691881/100000000000000 : ℝ)^4847
        have hw : |(2365492789/5000000000 : ℝ)|=(2365492789/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1756_s1_4 (p : ℝ) (hpa : (5855/1024 : ℝ) ≤ p) (hpb : p ≤ (5871/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1189072393/10000000000 : ℝ)*x 0 + (317973539/625000000 : ℝ)*x 1 + (2742317111/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1189072393/10000000000 : ℝ)^5871 ≤ (7582849813233/100000000000000 : ℝ)^4847 := by
    have hnat : (1189072393 : ℕ)^5871*100000000000000^4847 ≤ 7582849813233^4847*10000000000^5871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1189072393 10000000000 7582849813233 100000000000000 5871 4847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (317973539/625000000 : ℝ)^5871 ≤ (8821391271991/20000000000000 : ℝ)^4847 := by
    have hnat : (317973539 : ℕ)^5871*20000000000000^4847 ≤ 8821391271991^4847*625000000^5871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      317973539 625000000 8821391271991 20000000000000 5871 4847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2742317111/5000000000 : ℝ)^5871 ≤ (48310193811041/100000000000000 : ℝ)^4847 := by
    have hnat : (2742317111 : ℕ)^5871*100000000000000^4847 ≤ 48310193811041^4847*5000000000^5871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2742317111 5000000000 48310193811041 100000000000000 5871 4847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5871/1024 : ℝ)) 5871 4847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1189072393/10000000000 : ℝ), (317973539/625000000 : ℝ), (2742317111/5000000000 : ℝ)] ![(7582849813233/100000000000000 : ℝ), (8821391271991/20000000000000 : ℝ), (48310193811041/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1189072393/10000000000 : ℝ)|^5871 ≤ (7582849813233/100000000000000 : ℝ)^4847
        have hw : |(-1189072393/10000000000 : ℝ)|=(1189072393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(317973539/625000000 : ℝ)|^5871 ≤ (8821391271991/20000000000000 : ℝ)^4847
        have hw : |(317973539/625000000 : ℝ)|=(317973539/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2742317111/5000000000 : ℝ)|^5871 ≤ (48310193811041/100000000000000 : ℝ)^4847
        have hw : |(2742317111/5000000000 : ℝ)|=(2742317111/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1756_s1_5 (p : ℝ) (hpa : (5855/1024 : ℝ) ≤ p) (hpb : p ≤ (5871/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5224081663/10000000000 : ℝ)*x 0 + (-39985721/400000000 : ℝ)*x 1 + (5484634117/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5224081663/10000000000 : ℝ)^5871 ≤ (45544445137587/100000000000000 : ℝ)^4847 := by
    have hnat : (5224081663 : ℕ)^5871*100000000000000^4847 ≤ 45544445137587^4847*10000000000^5871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5224081663 10000000000 45544445137587 100000000000000 5871 4847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (39985721/400000000 : ℝ)^5871 ≤ (6145362154551/100000000000000 : ℝ)^4847 := by
    have hnat : (39985721 : ℕ)^5871*100000000000000^4847 ≤ 6145362154551^4847*400000000^5871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      39985721 400000000 6145362154551 100000000000000 5871 4847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5484634117/10000000000 : ℝ)^5871 ≤ (2415509634539/5000000000000 : ℝ)^4847 := by
    have hnat : (5484634117 : ℕ)^5871*5000000000000^4847 ≤ 2415509634539^4847*10000000000^5871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5484634117 10000000000 2415509634539 5000000000000 5871 4847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5871/1024 : ℝ)) 5871 4847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5224081663/10000000000 : ℝ), (-39985721/400000000 : ℝ), (5484634117/10000000000 : ℝ)] ![(45544445137587/100000000000000 : ℝ), (6145362154551/100000000000000 : ℝ), (2415509634539/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5224081663/10000000000 : ℝ)|^5871 ≤ (45544445137587/100000000000000 : ℝ)^4847
        have hw : |(5224081663/10000000000 : ℝ)|=(5224081663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-39985721/400000000 : ℝ)|^5871 ≤ (6145362154551/100000000000000 : ℝ)^4847
        have hw : |(-39985721/400000000 : ℝ)|=(39985721/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5484634117/10000000000 : ℝ)|^5871 ≤ (2415509634539/5000000000000 : ℝ)^4847
        have hw : |(5484634117/10000000000 : ℝ)|=(5484634117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1756_s1_6 (p : ℝ) (hpa : (5855/1024 : ℝ) ≤ p) (hpb : p ≤ (5871/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1044816237/2000000000 : ℝ)*x 0 + (5484634471/10000000000 : ℝ)*x 1 + (-249910799/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1044816237/2000000000 : ℝ)^5871 ≤ (455444400899/1000000000000 : ℝ)^4847 := by
    have hnat : (1044816237 : ℕ)^5871*1000000000000^4847 ≤ 455444400899^4847*2000000000^5871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1044816237 2000000000 455444400899 1000000000000 5871 4847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5484634471/10000000000 : ℝ)^5871 ≤ (24155098233831/50000000000000 : ℝ)^4847 := by
    have hnat : (5484634471 : ℕ)^5871*50000000000000^4847 ≤ 24155098233831^4847*10000000000^5871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5484634471 10000000000 24155098233831 50000000000000 5871 4847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (249910799/2500000000 : ℝ)^5871 ≤ (192042607121/3125000000000 : ℝ)^4847 := by
    have hnat : (249910799 : ℕ)^5871*3125000000000^4847 ≤ 192042607121^4847*2500000000^5871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      249910799 2500000000 192042607121 3125000000000 5871 4847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5871/1024 : ℝ)) 5871 4847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1044816237/2000000000 : ℝ), (5484634471/10000000000 : ℝ), (-249910799/2500000000 : ℝ)] ![(455444400899/1000000000000 : ℝ), (24155098233831/50000000000000 : ℝ), (192042607121/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1044816237/2000000000 : ℝ)|^5871 ≤ (455444400899/1000000000000 : ℝ)^4847
        have hw : |(1044816237/2000000000 : ℝ)|=(1044816237/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5484634471/10000000000 : ℝ)|^5871 ≤ (24155098233831/50000000000000 : ℝ)^4847
        have hw : |(5484634471/10000000000 : ℝ)|=(5484634471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-249910799/2500000000 : ℝ)|^5871 ≤ (192042607121/3125000000000 : ℝ)^4847
        have hw : |(-249910799/2500000000 : ℝ)|=(249910799/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1756_s1_7 (p : ℝ) (hpa : (5855/1024 : ℝ) ≤ p) (hpb : p ≤ (5871/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4009112729/10000000000 : ℝ)*x 0 + (235400897/500000000 : ℝ)*x 1 + (1685735223/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4009112729/10000000000 : ℝ)^5871 ≤ (3305113510879/10000000000000 : ℝ)^4847 := by
    have hnat : (4009112729 : ℕ)^5871*10000000000000^4847 ≤ 3305113510879^4847*10000000000^5871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4009112729 10000000000 3305113510879 10000000000000 5871 4847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (235400897/500000000 : ℝ)^5871 ≤ (40153217417891/100000000000000 : ℝ)^4847 := by
    have hnat : (235400897 : ℕ)^5871*100000000000000^4847 ≤ 40153217417891^4847*500000000^5871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      235400897 500000000 40153217417891 100000000000000 5871 4847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1685735223/5000000000 : ℝ)^5871 ≤ (5359129491259/20000000000000 : ℝ)^4847 := by
    have hnat : (1685735223 : ℕ)^5871*20000000000000^4847 ≤ 5359129491259^4847*5000000000^5871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1685735223 5000000000 5359129491259 20000000000000 5871 4847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5871/1024 : ℝ)) 5871 4847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4009112729/10000000000 : ℝ), (235400897/500000000 : ℝ), (1685735223/5000000000 : ℝ)] ![(3305113510879/10000000000000 : ℝ), (40153217417891/100000000000000 : ℝ), (5359129491259/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4009112729/10000000000 : ℝ)|^5871 ≤ (3305113510879/10000000000000 : ℝ)^4847
        have hw : |(4009112729/10000000000 : ℝ)|=(4009112729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(235400897/500000000 : ℝ)|^5871 ≤ (40153217417891/100000000000000 : ℝ)^4847
        have hw : |(235400897/500000000 : ℝ)|=(235400897/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1685735223/5000000000 : ℝ)|^5871 ≤ (5359129491259/20000000000000 : ℝ)^4847
        have hw : |(1685735223/5000000000 : ℝ)|=(1685735223/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1756_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5855/1024 : ℝ) ≤ p) (hpb : p ≤ (5871/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (43661367/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (20503/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (6957/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2267/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (17913/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (20503/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (6957/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (20503/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (6957/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (20503/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (6957/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (20503/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (6957/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (20503/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (6957/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (20503/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (6957/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (6957/100000 : ℝ) ^ (5855/1024 : ℝ) ≤ (4811287118309/20000000000000000000 : ℝ) := by
    have hpowers : (6957/100000 : ℝ)^5855 ≤ (4811287118309/20000000000000000000 : ℝ)^1024 := by
      have hnat : (6957 : ℕ)^5855*20000000000000000000^1024 ≤ 4811287118309^1024*100000^5855 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6957 100000 4811287118309 20000000000000000000 5855 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6957/100000 : ℝ)) (X := (4811287118309/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5855 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (20503/100000 : ℝ) ^ (5855/1024 : ℝ) ≤ (2904476621376593/25000000000000000000 : ℝ) := by
    have hpowers : (20503/100000 : ℝ)^5855 ≤ (2904476621376593/25000000000000000000 : ℝ)^1024 := by
      have hnat : (20503 : ℕ)^5855*25000000000000000000^1024 ≤ 2904476621376593^1024*100000^5855 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20503 100000 2904476621376593 25000000000000000000 5855 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (20503/100000 : ℝ)) (X := (2904476621376593/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5855 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000004811287118309/10000000000000000000 : ℝ) ≤ (2500000210365373/2500000000000000 : ℝ) ^ (5855/1024 : ℝ) := by
    have hpowers : (10000004811287118309/10000000000000000000 : ℝ)^1024 ≤ (2500000210365373/2500000000000000 : ℝ)^5855 := by
      have hnat : (10000004811287118309 : ℕ)^1024*2500000000000000^5855 ≤ 2500000210365373^5855*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000004811287118309 10000000000000000000 2500000210365373 2500000000000000 1024 5855 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500000210365373/2500000000000000 : ℝ)) (X := (10000004811287118309/10000000000000000000 : ℝ)) (by norm_num) 5855 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100011641962921097917/100000000000000000000 : ℝ) ≤ (625012725018677/625000000000000 : ℝ) ^ (5855/1024 : ℝ) := by
    have hpowers : (100011641962921097917/100000000000000000000 : ℝ)^1024 ≤ (625012725018677/625000000000000 : ℝ)^5855 := by
      have hnat : (100011641962921097917 : ℕ)^1024*625000000000000^5855 ≤ 625012725018677^5855*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100011641962921097917 100000000000000000000 625012725018677 625000000000000 1024 5855 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625012725018677/625000000000000 : ℝ)) (X := (100011641962921097917/100000000000000000000 : ℝ)) (by norm_num) 5855 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12502904476621376593/12500000000000000000 : ℝ) ≤ (2500101589784043/2500000000000000 : ℝ) ^ (5855/1024 : ℝ) := by
    have hpowers : (12502904476621376593/12500000000000000000 : ℝ)^1024 ≤ (2500101589784043/2500000000000000 : ℝ)^5855 := by
      have hnat : (12502904476621376593 : ℕ)^1024*2500000000000000^5855 ≤ 2500101589784043^5855*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12502904476621376593 12500000000000000000 2500101589784043 2500000000000000 1024 5855 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500101589784043/2500000000000000 : ℝ)) (X := (12502904476621376593/12500000000000000000 : ℝ)) (by norm_num) 5855 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4811287118309/20000000000000000000 : ℝ) ≤ ((8466074388248413867/8466250000000000000 : ℝ)+2*(10137941867/67730000000000 : ℝ)*(6957/100000 : ℝ))^(5855/1024 : ℝ) := by
    rw [show (8466074388248413867/8466250000000000000 : ℝ)+2*(10137941867/67730000000000 : ℝ)*(6957/100000 : ℝ)=(2500000210365373/2500000000000000 : ℝ) by norm_num, show 1+2*(4811287118309/20000000000000000000 : ℝ)=(10000004811287118309/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2904476621376593/25000000000000000000 : ℝ)+(4811287118309/20000000000000000000 : ℝ) ≤ ((8466074388248413867/8466250000000000000 : ℝ)+(10137941867/67730000000000 : ℝ)*((20503/100000 : ℝ)+(6957/100000 : ℝ)))^(5855/1024 : ℝ) := by
    rw [show (8466074388248413867/8466250000000000000 : ℝ)+(10137941867/67730000000000 : ℝ)*((20503/100000 : ℝ)+(6957/100000 : ℝ))=(625012725018677/625000000000000 : ℝ) by norm_num, show 1+(2904476621376593/25000000000000000000 : ℝ)+(4811287118309/20000000000000000000 : ℝ)=(100011641962921097917/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2904476621376593/25000000000000000000 : ℝ) ≤ ((8466074388248413867/8466250000000000000 : ℝ)+2*(10137941867/67730000000000 : ℝ)*(20503/100000 : ℝ))^(5855/1024 : ℝ) := by
    rw [show (8466074388248413867/8466250000000000000 : ℝ)+2*(10137941867/67730000000000 : ℝ)*(20503/100000 : ℝ)=(2500101589784043/2500000000000000 : ℝ) by norm_num, show 1+2*(2904476621376593/25000000000000000000 : ℝ)=(12502904476621376593/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (8466074388248413867/8466250000000000000 : ℝ)*(X 1 0+X 2 0)+(10137941867/67730000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5855/1024 : ℝ)) (lo := (6957/100000 : ℝ)) (hi := (20503/100000 : ℝ)) (c := (8466074388248413867/8466250000000000000 : ℝ)) (alpha := (10137941867/67730000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (8466074388248413867/8466250000000000000 : ℝ)*(X 0 1+X 2 1)+(10137941867/67730000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5855/1024 : ℝ)) (lo := (6957/100000 : ℝ)) (hi := (20503/100000 : ℝ)) (c := (8466074388248413867/8466250000000000000 : ℝ)) (alpha := (10137941867/67730000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (8466074388248413867/8466250000000000000 : ℝ)*(X 0 2+X 1 2)+(10137941867/67730000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5855/1024 : ℝ)) (lo := (6957/100000 : ℝ)) (hi := (20503/100000 : ℝ)) (c := (8466074388248413867/8466250000000000000 : ℝ)) (alpha := (10137941867/67730000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-237744247/2000000000 : ℝ)*X 0 0+(5491601337/10000000000 : ℝ)*X 0 1+(5080754393/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1756_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2666406733/5000000000 : ℝ)*X 1 0+(-1403522623/10000000000 : ℝ)*X 1 1+(5080753893/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1756_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5332811737/10000000000 : ℝ)*X 2 0+(40646041/80000000 : ℝ)*X 2 1+(-1403523299/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1756_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1001983407/2500000000 : ℝ)*X 0 0+(1674008549/5000000000 : ℝ)*X 0 1+(2365492789/5000000000 : ℝ)*X 0 2+(1001983407/2500000000 : ℝ)*X 1 0+(1674008549/5000000000 : ℝ)*X 1 1+(2365492789/5000000000 : ℝ)*X 1 2+(1001983407/2500000000 : ℝ)*X 2 0+(1674008549/5000000000 : ℝ)*X 2 1+(2365492789/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1756_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1189072393/10000000000 : ℝ)*X 0 0+(317973539/625000000 : ℝ)*X 0 1+(2742317111/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1756_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5224081663/10000000000 : ℝ)*X 1 0+(-39985721/400000000 : ℝ)*X 1 1+(5484634117/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1756_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1044816237/2000000000 : ℝ)*X 2 0+(5484634471/10000000000 : ℝ)*X 2 1+(-249910799/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1756_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4009112729/10000000000 : ℝ)*X 0 0+(235400897/500000000 : ℝ)*X 0 1+(1685735223/5000000000 : ℝ)*X 0 2+(4009112729/10000000000 : ℝ)*X 1 0+(235400897/500000000 : ℝ)*X 1 1+(1685735223/5000000000 : ℝ)*X 1 2+(4009112729/10000000000 : ℝ)*X 2 0+(235400897/500000000 : ℝ)*X 2 1+(1685735223/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1756_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (37125311742190143203037/6773000000000000000000000000 : ℝ) := by norm_num
    linear_combination (372632527/50000000000000 : ℝ)*(base19) + (8660583/100000000000000 : ℝ)*(upper2) + (91438199/50000000000000 : ℝ)*(upper3) + (20504467/50000000000000 : ℝ)*(lower4) + (197318150541141/12500000000000 : ℝ)*(major0) + (197318150541141/12500000000000 : ℝ)*(major1) + (197318150541141/12500000000000 : ℝ)*(major2) + (608500782023813/25000000000000 : ℝ)*(sp0) + (1217001959435507/50000000000000 : ℝ)*(sp1) + (1217001124216987/50000000000000 : ℝ)*(sp2) + (8826707162/1220703125 : ℝ)*(sp3) + (1536040817/100000000000000 : ℝ)*(sp4) + (1207851047/50000000000000 : ℝ)*(sp6) + (427774711/25000000000000 : ℝ)*(sp7) + (144617112361977/20000000000000 : ℝ)*(f.failure) + (608501166034017/25000000000000 : ℝ)*(f.sum) + (5433981779517/6773000000000000000000000000 : ℝ)*base65 + (59913586102983481/8140625000000000000000000000000 : ℝ)*base68 + (5988925462922769/8140625000000000000000000000000 : ℝ)*base69 + (9741089979045981/8140625000000000000000000000000 : ℝ)*base72 + (11314716797809/3386500000000000000000000000 : ℝ)*base73 + (39228106026485269/8140625000000000000000000000000 : ℝ)*base75 + (3806409131920981/8140625000000000000000000000000 : ℝ)*base78 + (14831310191829019/8140625000000000000000000000000 : ℝ)*base79 + (4877823011289/677300000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (2642559/400000000000000000000 : ℝ)*base89 + (2642559/400000000000000000000 : ℝ)*base91 + (2642559/400000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (10171036023058280124604533/3307128906250000000000000000000 : ℝ) := by norm_num
    linear_combination (482026071/100000000000000 : ℝ)*(base19) + (608704369/100000000000000 : ℝ)*(base23) + (98647889/50000000000000 : ℝ)*(upper2) + (59232641/100000000000000 : ℝ)*(upper3) + (254496911/100000000000000 : ℝ)*(upper5) + (408340201822103/25000000000000 : ℝ)*(major0) + (408340201822103/25000000000000 : ℝ)*(major1) + (408340201822103/25000000000000 : ℝ)*(major2) + (653536519/20000000000000 : ℝ)*(sp1) + (2280650497/100000000000000 : ℝ)*(sp2) + (157407907485899/6250000000000 : ℝ)*(sp4) + (1259261385032859/50000000000000 : ℝ)*(sp5) + (2518523630419519/100000000000000 : ℝ)*(sp6) + (748194992286161/100000000000000 : ℝ)*(sp7) + (748194992286161/100000000000000 : ℝ)*(f.failure) + (157407907485899/6250000000000 : ℝ)*(f.sum) + (30866774669147/6773000000000000000000000000 : ℝ)*base65 + (30607838709399823/16281250000000000000000000000000 : ℝ)*base68 + (21652159648712323/16281250000000000000000000000000 : ℝ)*base70 + (77754573133056073/16281250000000000000000000000000 : ℝ)*base72 + (26309207743443/6773000000000000000000000000 : ℝ)*base73 + (65678680037868573/16281250000000000000000000000000 : ℝ)*base76 + (30962171241943927/16281250000000000000000000000000 : ℝ)*base77 + (181580401369337323/16281250000000000000000000000000 : ℝ)*base80 + (8487001221141/6773000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (4442087/2000000000000000000000 : ℝ)*base89 + (4442087/2000000000000000000000 : ℝ)*base91 + (4442087/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1756_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5855/1024 : ℝ) ≤ p) (hpb : p ≤ (5871/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (43661367/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (20503/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (6957/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2267/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17913/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1756_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1756_s2_0 (p : ℝ) (hpa : (5855/1024 : ℝ) ≤ p) (hpb : p ≤ (5871/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1189505817/10000000000 : ℝ)*x 0 + (2744539047/5000000000 : ℝ)*x 1 + (317671371/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1189505817/10000000000 : ℝ)^5871 ≤ (7586197870631/100000000000000 : ℝ)^4847 := by
    have hnat : (1189505817 : ℕ)^5871*100000000000000^4847 ≤ 7586197870631^4847*10000000000^5871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1189505817 10000000000 7586197870631 100000000000000 5871 4847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2744539047/5000000000 : ℝ)^5871 ≤ (12089402560819/25000000000000 : ℝ)^4847 := by
    have hnat : (2744539047 : ℕ)^5871*25000000000000^4847 ≤ 12089402560819^4847*5000000000^5871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2744539047 5000000000 12089402560819 25000000000000 5871 4847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (317671371/625000000 : ℝ)^5871 ≤ (11014047967361/25000000000000 : ℝ)^4847 := by
    have hnat : (317671371 : ℕ)^5871*25000000000000^4847 ≤ 11014047967361^4847*625000000^5871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      317671371 625000000 11014047967361 25000000000000 5871 4847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5871/1024 : ℝ)) 5871 4847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1189505817/10000000000 : ℝ), (2744539047/5000000000 : ℝ), (317671371/625000000 : ℝ)] ![(7586197870631/100000000000000 : ℝ), (12089402560819/25000000000000 : ℝ), (11014047967361/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1189505817/10000000000 : ℝ)|^5871 ≤ (7586197870631/100000000000000 : ℝ)^4847
        have hw : |(-1189505817/10000000000 : ℝ)|=(1189505817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2744539047/5000000000 : ℝ)|^5871 ≤ (12089402560819/25000000000000 : ℝ)^4847
        have hw : |(2744539047/5000000000 : ℝ)|=(2744539047/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(317671371/625000000 : ℝ)|^5871 ≤ (11014047967361/25000000000000 : ℝ)^4847
        have hw : |(317671371/625000000 : ℝ)|=(317671371/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1756_s2_1 (p : ℝ) (hpa : (5855/1024 : ℝ) ≤ p) (hpb : p ≤ (5871/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (333256861/625000000 : ℝ)*x 0 + (-17523079/125000000 : ℝ)*x 1 + (317671371/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (333256861/625000000 : ℝ)^5871 ≤ (5835962754169/12500000000000 : ℝ)^4847 := by
    have hnat : (333256861 : ℕ)^5871*12500000000000^4847 ≤ 5835962754169^4847*625000000^5871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      333256861 625000000 5835962754169 12500000000000 5871 4847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (17523079/125000000 : ℝ)^5871 ≤ (462805304087/5000000000000 : ℝ)^4847 := by
    have hnat : (17523079 : ℕ)^5871*5000000000000^4847 ≤ 462805304087^4847*125000000^5871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      17523079 125000000 462805304087 5000000000000 5871 4847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (317671371/625000000 : ℝ)^5871 ≤ (11014047967361/25000000000000 : ℝ)^4847 := by
    have hnat : (317671371 : ℕ)^5871*25000000000000^4847 ≤ 11014047967361^4847*625000000^5871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      317671371 625000000 11014047967361 25000000000000 5871 4847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5871/1024 : ℝ)) 5871 4847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(333256861/625000000 : ℝ), (-17523079/125000000 : ℝ), (317671371/625000000 : ℝ)] ![(5835962754169/12500000000000 : ℝ), (462805304087/5000000000000 : ℝ), (11014047967361/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(333256861/625000000 : ℝ)|^5871 ≤ (5835962754169/12500000000000 : ℝ)^4847
        have hw : |(333256861/625000000 : ℝ)|=(333256861/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-17523079/125000000 : ℝ)|^5871 ≤ (462805304087/5000000000000 : ℝ)^4847
        have hw : |(-17523079/125000000 : ℝ)|=(17523079/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(317671371/625000000 : ℝ)|^5871 ≤ (11014047967361/25000000000000 : ℝ)^4847
        have hw : |(317671371/625000000 : ℝ)|=(317671371/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1756_s2_2 (p : ℝ) (hpa : (5855/1024 : ℝ) ≤ p) (hpb : p ≤ (5871/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (333256861/625000000 : ℝ)*x 0 + (5082741937/10000000000 : ℝ)*x 1 + (-17523079/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (333256861/625000000 : ℝ)^5871 ≤ (5835962754169/12500000000000 : ℝ)^4847 := by
    have hnat : (333256861 : ℕ)^5871*12500000000000^4847 ≤ 5835962754169^4847*625000000^5871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      333256861 625000000 5835962754169 12500000000000 5871 4847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5082741937/10000000000 : ℝ)^5871 ≤ (44056191879943/100000000000000 : ℝ)^4847 := by
    have hnat : (5082741937 : ℕ)^5871*100000000000000^4847 ≤ 44056191879943^4847*10000000000^5871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5082741937 10000000000 44056191879943 100000000000000 5871 4847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (17523079/125000000 : ℝ)^5871 ≤ (462805304087/5000000000000 : ℝ)^4847 := by
    have hnat : (17523079 : ℕ)^5871*5000000000000^4847 ≤ 462805304087^4847*125000000^5871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      17523079 125000000 462805304087 5000000000000 5871 4847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5871/1024 : ℝ)) 5871 4847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(333256861/625000000 : ℝ), (5082741937/10000000000 : ℝ), (-17523079/125000000 : ℝ)] ![(5835962754169/12500000000000 : ℝ), (44056191879943/100000000000000 : ℝ), (462805304087/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(333256861/625000000 : ℝ)|^5871 ≤ (5835962754169/12500000000000 : ℝ)^4847
        have hw : |(333256861/625000000 : ℝ)|=(333256861/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5082741937/10000000000 : ℝ)|^5871 ≤ (44056191879943/100000000000000 : ℝ)^4847
        have hw : |(5082741937/10000000000 : ℝ)|=(5082741937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-17523079/125000000 : ℝ)|^5871 ≤ (462805304087/5000000000000 : ℝ)^4847
        have hw : |(-17523079/125000000 : ℝ)|=(17523079/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1756_s2_3 (p : ℝ) (hpa : (5855/1024 : ℝ) ≤ p) (hpb : p ≤ (5871/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (20042893/50000000 : ℝ)*x 0 + (335556271/1000000000 : ℝ)*x 1 + (29520911/62500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (20042893/50000000 : ℝ)^5871 ≤ (1032681298387/3125000000000 : ℝ)^4847 := by
    have hnat : (20042893 : ℕ)^5871*3125000000000^4847 ≤ 1032681298387^4847*50000000^5871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20042893 50000000 1032681298387 3125000000000 5871 4847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (335556271/1000000000 : ℝ)^5871 ≤ (13321291288329/50000000000000 : ℝ)^4847 := by
    have hnat : (335556271 : ℕ)^5871*50000000000000^4847 ≤ 13321291288329^4847*1000000000^5871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      335556271 1000000000 13321291288329 50000000000000 5871 4847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (29520911/62500000 : ℝ)^5871 ≤ (8062323171329/20000000000000 : ℝ)^4847 := by
    have hnat : (29520911 : ℕ)^5871*20000000000000^4847 ≤ 8062323171329^4847*62500000^5871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      29520911 62500000 8062323171329 20000000000000 5871 4847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5871/1024 : ℝ)) 5871 4847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(20042893/50000000 : ℝ), (335556271/1000000000 : ℝ), (29520911/62500000 : ℝ)] ![(1032681298387/3125000000000 : ℝ), (13321291288329/50000000000000 : ℝ), (8062323171329/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(20042893/50000000 : ℝ)|^5871 ≤ (1032681298387/3125000000000 : ℝ)^4847
        have hw : |(20042893/50000000 : ℝ)|=(20042893/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(335556271/1000000000 : ℝ)|^5871 ≤ (13321291288329/50000000000000 : ℝ)^4847
        have hw : |(335556271/1000000000 : ℝ)|=(335556271/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(29520911/62500000 : ℝ)|^5871 ≤ (8062323171329/20000000000000 : ℝ)^4847
        have hw : |(29520911/62500000 : ℝ)|=(29520911/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1756_s2_4 (p : ℝ) (hpa : (5855/1024 : ℝ) ≤ p) (hpb : p ≤ (5871/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1189844723/10000000000 : ℝ)*x 0 + (39761063/78125000 : ℝ)*x 1 + (274113219/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1189844723/10000000000 : ℝ)^5871 ≤ (1897203996807/25000000000000 : ℝ)^4847 := by
    have hnat : (1189844723 : ℕ)^5871*25000000000000^4847 ≤ 1897203996807^4847*10000000000^5871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1189844723 10000000000 1897203996807 25000000000000 5871 4847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (39761063/78125000 : ℝ)^5871 ≤ (44126273258479/100000000000000 : ℝ)^4847 := by
    have hnat : (39761063 : ℕ)^5871*100000000000000^4847 ≤ 44126273258479^4847*78125000^5871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      39761063 78125000 44126273258479 100000000000000 5871 4847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (274113219/500000000 : ℝ)^5871 ≤ (48284910745039/100000000000000 : ℝ)^4847 := by
    have hnat : (274113219 : ℕ)^5871*100000000000000^4847 ≤ 48284910745039^4847*500000000^5871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      274113219 500000000 48284910745039 100000000000000 5871 4847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5871/1024 : ℝ)) 5871 4847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1189844723/10000000000 : ℝ), (39761063/78125000 : ℝ), (274113219/500000000 : ℝ)] ![(1897203996807/25000000000000 : ℝ), (44126273258479/100000000000000 : ℝ), (48284910745039/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1189844723/10000000000 : ℝ)|^5871 ≤ (1897203996807/25000000000000 : ℝ)^4847
        have hw : |(-1189844723/10000000000 : ℝ)|=(1189844723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(39761063/78125000 : ℝ)|^5871 ≤ (44126273258479/100000000000000 : ℝ)^4847
        have hw : |(39761063/78125000 : ℝ)|=(39761063/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(274113219/500000000 : ℝ)|^5871 ≤ (48284910745039/100000000000000 : ℝ)^4847
        have hw : |(274113219/500000000 : ℝ)|=(274113219/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1756_s2_5 (p : ℝ) (hpa : (5855/1024 : ℝ) ≤ p) (hpb : p ≤ (5871/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5224584823/10000000000 : ℝ)*x 0 + (-1002323933/10000000000 : ℝ)*x 1 + (2741132189/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5224584823/10000000000 : ℝ)^5871 ≤ (22774879284297/50000000000000 : ℝ)^4847 := by
    have hnat : (5224584823 : ℕ)^5871*50000000000000^4847 ≤ 22774879284297^4847*10000000000^5871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5224584823 10000000000 22774879284297 50000000000000 5871 4847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1002323933/10000000000 : ℝ)^5871 ≤ (6165330700447/100000000000000 : ℝ)^4847 := by
    have hnat : (1002323933 : ℕ)^5871*100000000000000^4847 ≤ 6165330700447^4847*10000000000^5871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1002323933 10000000000 6165330700447 100000000000000 5871 4847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2741132189/5000000000 : ℝ)^5871 ≤ (24142455361851/50000000000000 : ℝ)^4847 := by
    have hnat : (2741132189 : ℕ)^5871*50000000000000^4847 ≤ 24142455361851^4847*5000000000^5871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2741132189 5000000000 24142455361851 50000000000000 5871 4847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5871/1024 : ℝ)) 5871 4847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5224584823/10000000000 : ℝ), (-1002323933/10000000000 : ℝ), (2741132189/5000000000 : ℝ)] ![(22774879284297/50000000000000 : ℝ), (6165330700447/100000000000000 : ℝ), (24142455361851/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5224584823/10000000000 : ℝ)|^5871 ≤ (22774879284297/50000000000000 : ℝ)^4847
        have hw : |(5224584823/10000000000 : ℝ)|=(5224584823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1002323933/10000000000 : ℝ)|^5871 ≤ (6165330700447/100000000000000 : ℝ)^4847
        have hw : |(-1002323933/10000000000 : ℝ)|=(1002323933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2741132189/5000000000 : ℝ)|^5871 ≤ (24142455361851/50000000000000 : ℝ)^4847
        have hw : |(2741132189/5000000000 : ℝ)|=(2741132189/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1756_s2_6 (p : ℝ) (hpa : (5855/1024 : ℝ) ≤ p) (hpb : p ≤ (5871/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5224584911/10000000000 : ℝ)*x 0 + (5482264317/10000000000 : ℝ)*x 1 + (-501161947/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5224584911/10000000000 : ℝ)^5871 ≤ (22774879748947/50000000000000 : ℝ)^4847 := by
    have hnat : (5224584911 : ℕ)^5871*50000000000000^4847 ≤ 22774879748947^4847*10000000000^5871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5224584911 10000000000 22774879748947 50000000000000 5871 4847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5482264317/10000000000 : ℝ)^5871 ≤ (48284910072943/100000000000000 : ℝ)^4847 := by
    have hnat : (5482264317 : ℕ)^5871*100000000000000^4847 ≤ 48284910072943^4847*10000000000^5871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5482264317 10000000000 48284910072943 100000000000000 5871 4847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (501161947/5000000000 : ℝ)^5871 ≤ (1541332602469/25000000000000 : ℝ)^4847 := by
    have hnat : (501161947 : ℕ)^5871*25000000000000^4847 ≤ 1541332602469^4847*5000000000^5871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      501161947 5000000000 1541332602469 25000000000000 5871 4847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5871/1024 : ℝ)) 5871 4847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5224584911/10000000000 : ℝ), (5482264317/10000000000 : ℝ), (-501161947/5000000000 : ℝ)] ![(22774879748947/50000000000000 : ℝ), (48284910072943/100000000000000 : ℝ), (1541332602469/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5224584911/10000000000 : ℝ)|^5871 ≤ (22774879748947/50000000000000 : ℝ)^4847
        have hw : |(5224584911/10000000000 : ℝ)|=(5224584911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5482264317/10000000000 : ℝ)|^5871 ≤ (48284910072943/100000000000000 : ℝ)^4847
        have hw : |(5482264317/10000000000 : ℝ)|=(5482264317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-501161947/5000000000 : ℝ)|^5871 ≤ (1541332602469/25000000000000 : ℝ)^4847
        have hw : |(-501161947/5000000000 : ℝ)|=(501161947/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1756_s2_7 (p : ℝ) (hpa : (5855/1024 : ℝ) ≤ p) (hpb : p ≤ (5871/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4009719219/10000000000 : ℝ)*x 0 + (1175219889/2500000000 : ℝ)*x 1 + (675699743/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4009719219/10000000000 : ℝ)^5871 ≤ (16528595707019/50000000000000 : ℝ)^4847 := by
    have hnat : (4009719219 : ℕ)^5871*50000000000000^4847 ≤ 16528595707019^4847*10000000000^5871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4009719219 10000000000 16528595707019 50000000000000 5871 4847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1175219889/2500000000 : ℝ)^5871 ≤ (4007948616431/10000000000000 : ℝ)^4847 := by
    have hnat : (1175219889 : ℕ)^5871*10000000000000^4847 ≤ 4007948616431^4847*2500000000^5871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1175219889 2500000000 4007948616431 10000000000000 5871 4847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (675699743/2000000000 : ℝ)^5871 ≤ (13431661200131/50000000000000 : ℝ)^4847 := by
    have hnat : (675699743 : ℕ)^5871*50000000000000^4847 ≤ 13431661200131^4847*2000000000^5871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      675699743 2000000000 13431661200131 50000000000000 5871 4847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5871/1024 : ℝ)) 5871 4847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4009719219/10000000000 : ℝ), (1175219889/2500000000 : ℝ), (675699743/2000000000 : ℝ)] ![(16528595707019/50000000000000 : ℝ), (4007948616431/10000000000000 : ℝ), (13431661200131/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4009719219/10000000000 : ℝ)|^5871 ≤ (16528595707019/50000000000000 : ℝ)^4847
        have hw : |(4009719219/10000000000 : ℝ)|=(4009719219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1175219889/2500000000 : ℝ)|^5871 ≤ (4007948616431/10000000000000 : ℝ)^4847
        have hw : |(1175219889/2500000000 : ℝ)|=(1175219889/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(675699743/2000000000 : ℝ)|^5871 ≤ (13431661200131/50000000000000 : ℝ)^4847
        have hw : |(675699743/2000000000 : ℝ)|=(675699743/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1756_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5855/1024 : ℝ) ≤ p) (hpb : p ≤ (5871/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (43661367/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17913/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2267/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (1139/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (893/5000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (17913/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2267/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (17913/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2267/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (17913/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2267/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (17913/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2267/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (17913/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2267/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (17913/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2267/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2267/25000 : ℝ) ^ (5855/1024 : ℝ) ≤ (109467956589387/100000000000000000000 : ℝ) := by
    have hpowers : (2267/25000 : ℝ)^5855 ≤ (109467956589387/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2267 : ℕ)^5855*100000000000000000000^1024 ≤ 109467956589387^1024*25000^5855 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2267 25000 109467956589387 100000000000000000000 5855 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2267/25000 : ℝ)) (X := (109467956589387/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5855 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (17913/100000 : ℝ) ^ (5855/1024 : ℝ) ≤ (1341917140482159/25000000000000000000 : ℝ) := by
    have hpowers : (17913/100000 : ℝ)^5855 ≤ (1341917140482159/25000000000000000000 : ℝ)^1024 := by
      have hnat : (17913 : ℕ)^5855*25000000000000000000^1024 ≤ 1341917140482159^1024*100000^5855 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17913 100000 1341917140482159 25000000000000000000 5855 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (17913/100000 : ℝ)) (X := (1341917140482159/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5855 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000109467956589387/50000000000000000000 : ℝ) ≤ (10000003829037961/10000000000000000 : ℝ) ^ (5855/1024 : ℝ) := by
    have hpowers : (50000109467956589387/50000000000000000000 : ℝ)^1024 ≤ (10000003829037961/10000000000000000 : ℝ)^5855 := by
      have hnat : (50000109467956589387 : ℕ)^1024*10000000000000000^5855 ≤ 10000003829037961^5855*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000109467956589387 50000000000000000000 10000003829037961 10000000000000000 1024 5855 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000003829037961/10000000000000000 : ℝ)) (X := (50000109467956589387/50000000000000000000 : ℝ)) (by norm_num) 5855 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100005477136518518023/100000000000000000000 : ℝ) ≤ (10000095789258189/10000000000000000 : ℝ) ^ (5855/1024 : ℝ) := by
    have hpowers : (100005477136518518023/100000000000000000000 : ℝ)^1024 ≤ (10000095789258189/10000000000000000 : ℝ)^5855 := by
      have hnat : (100005477136518518023 : ℕ)^1024*10000000000000000^5855 ≤ 10000095789258189^5855*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100005477136518518023 100000000000000000000 10000095789258189 10000000000000000 1024 5855 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000095789258189/10000000000000000 : ℝ)) (X := (100005477136518518023/100000000000000000000 : ℝ)) (by norm_num) 5855 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12501341917140482159/12500000000000000000 : ℝ) ≤ (10000187749478417/10000000000000000 : ℝ) ^ (5855/1024 : ℝ) := by
    have hpowers : (12501341917140482159/12500000000000000000 : ℝ)^1024 ≤ (10000187749478417/10000000000000000 : ℝ)^5855 := by
      have hnat : (12501341917140482159 : ℕ)^1024*10000000000000000^5855 ≤ 10000187749478417^5855*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12501341917140482159 12500000000000000000 10000187749478417 10000000000000000 1024 5855 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000187749478417/10000000000000000 : ℝ)) (X := (12501341917140482159/12500000000000000000 : ℝ)) (by norm_num) 5855 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(109467956589387/100000000000000000000 : ℝ) ≤ ((88448366077286710037/88450000000000000000 : ℝ)+2*(22990055057/221125000000000 : ℝ)*(2267/25000 : ℝ))^(5855/1024 : ℝ) := by
    rw [show (88448366077286710037/88450000000000000000 : ℝ)+2*(22990055057/221125000000000 : ℝ)*(2267/25000 : ℝ)=(10000003829037961/10000000000000000 : ℝ) by norm_num, show 1+2*(109467956589387/100000000000000000000 : ℝ)=(50000109467956589387/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1341917140482159/25000000000000000000 : ℝ)+(109467956589387/100000000000000000000 : ℝ) ≤ ((88448366077286710037/88450000000000000000 : ℝ)+(22990055057/221125000000000 : ℝ)*((17913/100000 : ℝ)+(2267/25000 : ℝ)))^(5855/1024 : ℝ) := by
    rw [show (88448366077286710037/88450000000000000000 : ℝ)+(22990055057/221125000000000 : ℝ)*((17913/100000 : ℝ)+(2267/25000 : ℝ))=(10000095789258189/10000000000000000 : ℝ) by norm_num, show 1+(1341917140482159/25000000000000000000 : ℝ)+(109467956589387/100000000000000000000 : ℝ)=(100005477136518518023/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1341917140482159/25000000000000000000 : ℝ) ≤ ((88448366077286710037/88450000000000000000 : ℝ)+2*(22990055057/221125000000000 : ℝ)*(17913/100000 : ℝ))^(5855/1024 : ℝ) := by
    rw [show (88448366077286710037/88450000000000000000 : ℝ)+2*(22990055057/221125000000000 : ℝ)*(17913/100000 : ℝ)=(10000187749478417/10000000000000000 : ℝ) by norm_num, show 1+2*(1341917140482159/25000000000000000000 : ℝ)=(12501341917140482159/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (88448366077286710037/88450000000000000000 : ℝ)*(X 1 0+X 2 0)+(22990055057/221125000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5855/1024 : ℝ)) (lo := (2267/25000 : ℝ)) (hi := (17913/100000 : ℝ)) (c := (88448366077286710037/88450000000000000000 : ℝ)) (alpha := (22990055057/221125000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (88448366077286710037/88450000000000000000 : ℝ)*(X 0 1+X 2 1)+(22990055057/221125000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5855/1024 : ℝ)) (lo := (2267/25000 : ℝ)) (hi := (17913/100000 : ℝ)) (c := (88448366077286710037/88450000000000000000 : ℝ)) (alpha := (22990055057/221125000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (88448366077286710037/88450000000000000000 : ℝ)*(X 0 2+X 1 2)+(22990055057/221125000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5855/1024 : ℝ)) (lo := (2267/25000 : ℝ)) (hi := (17913/100000 : ℝ)) (c := (88448366077286710037/88450000000000000000 : ℝ)) (alpha := (22990055057/221125000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1189505817/10000000000 : ℝ)*X 0 0+(2744539047/5000000000 : ℝ)*X 0 1+(317671371/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1756_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((333256861/625000000 : ℝ)*X 1 0+(-17523079/125000000 : ℝ)*X 1 1+(317671371/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1756_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((333256861/625000000 : ℝ)*X 2 0+(5082741937/10000000000 : ℝ)*X 2 1+(-17523079/125000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1756_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((20042893/50000000 : ℝ)*X 0 0+(335556271/1000000000 : ℝ)*X 0 1+(29520911/62500000 : ℝ)*X 0 2+(20042893/50000000 : ℝ)*X 1 0+(335556271/1000000000 : ℝ)*X 1 1+(29520911/62500000 : ℝ)*X 1 2+(20042893/50000000 : ℝ)*X 2 0+(335556271/1000000000 : ℝ)*X 2 1+(29520911/62500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1756_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1189844723/10000000000 : ℝ)*X 0 0+(39761063/78125000 : ℝ)*X 0 1+(274113219/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1756_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5224584823/10000000000 : ℝ)*X 1 0+(-1002323933/10000000000 : ℝ)*X 1 1+(2741132189/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1756_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5224584911/10000000000 : ℝ)*X 2 0+(5482264317/10000000000 : ℝ)*X 2 1+(-501161947/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1756_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4009719219/10000000000 : ℝ)*X 0 0+(1175219889/2500000000 : ℝ)*X 0 1+(675699743/2000000000 : ℝ)*X 0 2+(4009719219/10000000000 : ℝ)*X 1 0+(1175219889/2500000000 : ℝ)*X 1 1+(675699743/2000000000 : ℝ)*X 1 2+(4009719219/10000000000 : ℝ)*X 2 0+(1175219889/2500000000 : ℝ)*X 2 1+(675699743/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1756_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5254188593743184383270222089/884500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (202315821/25000000000000 : ℝ)*(base19) + (382278017/50000000000000 : ℝ)*(base23) + (5959599/25000000000000 : ℝ)*(lower2) + (71022247/50000000000000 : ℝ)*(upper3) + (27640447/25000000000000 : ℝ)*(upper5) + (319214352969801/20000000000000 : ℝ)*(major0) + (319214352969801/20000000000000 : ℝ)*(major1) + (319214352969801/20000000000000 : ℝ)*(major2) + (153813934892177/6250000000000 : ℝ)*(sp0) + (1230514276968497/50000000000000 : ℝ)*(sp1) + (615257149661061/25000000000000 : ℝ)*(sp2) + (365555953475849/50000000000000 : ℝ)*(sp3) + (3202462723/50000000000000 : ℝ)*(sp4) + (2061536281/100000000000000 : ℝ)*(sp7) + (731113968487979/100000000000000 : ℝ)*(f.failure) + (1230514681600139/50000000000000 : ℝ)*(f.sum) + (52899862037137/8845000000000000000000000000 : ℝ)*base66 + (5027244034624607363/1769000000000000000000000000000000 : ℝ)*base68 + (15385246861004392637/1769000000000000000000000000000000 : ℝ)*base69 + (7019375104940392637/1769000000000000000000000000000000 : ℝ)*base71 + (8772973181323/2211250000000000000000000000 : ℝ)*base74 + (13042361764116392637/1769000000000000000000000000000000 : ℝ)*base75 + (1441886339059607363/1769000000000000000000000000000000 : ℝ)*base78 + (12017131330731392637/1769000000000000000000000000000000 : ℝ)*base79 + (11056836583453/8845000000000000000000000000 : ℝ)*base81 + (13792707/2000000000000000000000 : ℝ)*base90 + (13792707/2000000000000000000000 : ℝ)*base92 + (13792707/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (14306103617199904208773791891/1105625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1658916603/100000000000000 : ℝ)*(base19) + (447077613/25000000000000 : ℝ)*(base23) + (473848911/100000000000000 : ℝ)*(lower1) + (137548327/50000000000000 : ℝ)*(upper3) + (37611487/100000000000000 : ℝ)*(lower4) + (282411397/100000000000000 : ℝ)*(upper5) + (825427010998981/50000000000000 : ℝ)*(major0) + (825427010998981/50000000000000 : ℝ)*(major1) + (825427010998981/50000000000000 : ℝ)*(major2) + (705980631/100000000000000 : ℝ)*(sp2) + (1272749744231507/50000000000000 : ℝ)*(sp4) + (2545497829546411/100000000000000 : ℝ)*(sp5) + (2545496994171931/100000000000000 : ℝ)*(sp6) + (756208124220189/100000000000000 : ℝ)*(sp7) + (756208124220189/100000000000000 : ℝ)*(f.failure) + (1272749744231507/50000000000000 : ℝ)*(f.sum) + (216731873546189/44225000000000000000000000000 : ℝ)*base66 + (25938126691033727703/4422500000000000000000000000000000 : ℝ)*base68 + (16009107704221227703/4422500000000000000000000000000000 : ℝ)*base70 + (20970861655073727703/4422500000000000000000000000000000 : ℝ)*base72 + (128302409513389/44225000000000000000000000000 : ℝ)*base74 + (62165629092723772297/4422500000000000000000000000000000 : ℝ)*base75 + (20879588083413727703/4422500000000000000000000000000000 : ℝ)*base78 + (17341898852488727703/4422500000000000000000000000000000 : ℝ)*base80 + (196254488196389/44225000000000000000000000000 : ℝ)*base82 + (20738363/2000000000000000000000 : ℝ)*base89 + (20738363/2000000000000000000000 : ℝ)*base91 + (20738363/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1756_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5855/1024 : ℝ) ≤ p) (hpb : p ≤ (5871/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (43661367/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17913/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2267/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1139/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (893/5000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1756_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1756_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5855/1024 : ℝ) ≤ p) (hpb : p ≤ (5871/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (43661367/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1139/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (893/5000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1756_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1756_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1756_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5855/1024 : ℝ) ≤ p) (hpb : p ≤ (5871/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (43661367/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1139/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (893/5000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1756_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
