-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1250_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:23:12.162554+00:00
-- url     : https://prove2.me/submissions/186f733c-b214-429f-8ca2-150acf8cbd3f

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
theorem support_rectangle_w1250_box_0 (p : ℝ) (hpa : (4221/1024 : ℝ) ≤ p) (hpb : p ≤ (8443/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1992843499/10000000000 : ℝ)*x 0 + (1343680047/2500000000 : ℝ)*x 1 + (5374720559/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1992843499/10000000000 : ℝ)^8443 ≤ (11888562568131/100000000000000 : ℝ)^6395 := by
    have hnat : (1992843499 : ℕ)^8443*100000000000000^6395 ≤ 11888562568131^6395*10000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1992843499 10000000000 11888562568131 100000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1343680047/2500000000 : ℝ)^8443 ≤ (8811143340281/20000000000000 : ℝ)^6395 := by
    have hnat : (1343680047 : ℕ)^8443*20000000000000^6395 ≤ 8811143340281^6395*2500000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1343680047 2500000000 8811143340281 20000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5374720559/10000000000 : ℝ)^8443 ≤ (22027860358161/50000000000000 : ℝ)^6395 := by
    have hnat : (5374720559 : ℕ)^8443*50000000000000^6395 ≤ 22027860358161^6395*10000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5374720559 10000000000 22027860358161 50000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8443/2048 : ℝ)) 8443 6395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1992843499/10000000000 : ℝ), (1343680047/2500000000 : ℝ), (5374720559/10000000000 : ℝ)] ![(11888562568131/100000000000000 : ℝ), (8811143340281/20000000000000 : ℝ), (22027860358161/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1992843499/10000000000 : ℝ)|^8443 ≤ (11888562568131/100000000000000 : ℝ)^6395
        have hw : |(-1992843499/10000000000 : ℝ)|=(1992843499/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1343680047/2500000000 : ℝ)|^8443 ≤ (8811143340281/20000000000000 : ℝ)^6395
        have hw : |(1343680047/2500000000 : ℝ)|=(1343680047/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5374720559/10000000000 : ℝ)|^8443 ≤ (22027860358161/50000000000000 : ℝ)^6395
        have hw : |(5374720559/10000000000 : ℝ)|=(5374720559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1250_box_1 (p : ℝ) (hpa : (4221/1024 : ℝ) ≤ p) (hpb : p ≤ (8443/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1324212703/2500000000 : ℝ)*x 0 + (-2098698741/10000000000 : ℝ)*x 1 + (2687360049/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1324212703/2500000000 : ℝ)^8443 ≤ (43214985203971/100000000000000 : ℝ)^6395 := by
    have hnat : (1324212703 : ℕ)^8443*100000000000000^6395 ≤ 43214985203971^6395*2500000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1324212703 2500000000 43214985203971 100000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2098698741/10000000000 : ℝ)^8443 ≤ (2545859810637/20000000000000 : ℝ)^6395 := by
    have hnat : (2098698741 : ℕ)^8443*20000000000000^6395 ≤ 2545859810637^6395*10000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2098698741 10000000000 2545859810637 20000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2687360049/5000000000 : ℝ)^8443 ≤ (11013928931859/25000000000000 : ℝ)^6395 := by
    have hnat : (2687360049 : ℕ)^8443*25000000000000^6395 ≤ 11013928931859^6395*5000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2687360049 5000000000 11013928931859 25000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8443/2048 : ℝ)) 8443 6395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1324212703/2500000000 : ℝ), (-2098698741/10000000000 : ℝ), (2687360049/5000000000 : ℝ)] ![(43214985203971/100000000000000 : ℝ), (2545859810637/20000000000000 : ℝ), (11013928931859/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1324212703/2500000000 : ℝ)|^8443 ≤ (43214985203971/100000000000000 : ℝ)^6395
        have hw : |(1324212703/2500000000 : ℝ)|=(1324212703/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2098698741/10000000000 : ℝ)|^8443 ≤ (2545859810637/20000000000000 : ℝ)^6395
        have hw : |(-2098698741/10000000000 : ℝ)|=(2098698741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2687360049/5000000000 : ℝ)|^8443 ≤ (11013928931859/25000000000000 : ℝ)^6395
        have hw : |(2687360049/5000000000 : ℝ)|=(2687360049/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1250_box_2 (p : ℝ) (hpa : (4221/1024 : ℝ) ≤ p) (hpb : p ≤ (8443/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5296850723/10000000000 : ℝ)*x 0 + (5374720689/10000000000 : ℝ)*x 1 + (-2098698061/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5296850723/10000000000 : ℝ)^8443 ≤ (8642996849063/20000000000000 : ℝ)^6395 := by
    have hnat : (5296850723 : ℕ)^8443*20000000000000^6395 ≤ 8642996849063^6395*10000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5296850723 10000000000 8642996849063 20000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5374720689/10000000000 : ℝ)^8443 ≤ (22027861061583/50000000000000 : ℝ)^6395 := by
    have hnat : (5374720689 : ℕ)^8443*50000000000000^6395 ≤ 22027861061583^6395*10000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5374720689 10000000000 22027861061583 50000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2098698061/10000000000 : ℝ)^8443 ≤ (12729293607913/100000000000000 : ℝ)^6395 := by
    have hnat : (2098698061 : ℕ)^8443*100000000000000^6395 ≤ 12729293607913^6395*10000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2098698061 10000000000 12729293607913 100000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8443/2048 : ℝ)) 8443 6395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5296850723/10000000000 : ℝ), (5374720689/10000000000 : ℝ), (-2098698061/10000000000 : ℝ)] ![(8642996849063/20000000000000 : ℝ), (22027861061583/50000000000000 : ℝ), (12729293607913/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5296850723/10000000000 : ℝ)|^8443 ≤ (8642996849063/20000000000000 : ℝ)^6395
        have hw : |(5296850723/10000000000 : ℝ)|=(5296850723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5374720689/10000000000 : ℝ)|^8443 ≤ (22027861061583/50000000000000 : ℝ)^6395
        have hw : |(5374720689/10000000000 : ℝ)|=(5374720689/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2098698061/10000000000 : ℝ)|^8443 ≤ (12729293607913/100000000000000 : ℝ)^6395
        have hw : |(-2098698061/10000000000 : ℝ)|=(2098698061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1250_box_3 (p : ℝ) (hpa : (4221/1024 : ℝ) ≤ p) (hpb : p ≤ (8443/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4456126803/10000000000 : ℝ)*x 0 + (4298492469/10000000000 : ℝ)*x 1 + (4298491639/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4456126803/10000000000 : ℝ)^8443 ≤ (8599558060243/25000000000000 : ℝ)^6395 := by
    have hnat : (4456126803 : ℕ)^8443*25000000000000^6395 ≤ 8599558060243^6395*10000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4456126803 10000000000 8599558060243 25000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4298492469/10000000000 : ℝ)^8443 ≤ (32800888055443/100000000000000 : ℝ)^6395 := by
    have hnat : (4298492469 : ℕ)^8443*100000000000000^6395 ≤ 32800888055443^6395*10000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4298492469 10000000000 32800888055443 100000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4298491639/10000000000 : ℝ)^8443 ≤ (16400439846783/50000000000000 : ℝ)^6395 := by
    have hnat : (4298491639 : ℕ)^8443*50000000000000^6395 ≤ 16400439846783^6395*10000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4298491639 10000000000 16400439846783 50000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8443/2048 : ℝ)) 8443 6395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4456126803/10000000000 : ℝ), (4298492469/10000000000 : ℝ), (4298491639/10000000000 : ℝ)] ![(8599558060243/25000000000000 : ℝ), (32800888055443/100000000000000 : ℝ), (16400439846783/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4456126803/10000000000 : ℝ)|^8443 ≤ (8599558060243/25000000000000 : ℝ)^6395
        have hw : |(4456126803/10000000000 : ℝ)|=(4456126803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4298492469/10000000000 : ℝ)|^8443 ≤ (32800888055443/100000000000000 : ℝ)^6395
        have hw : |(4298492469/10000000000 : ℝ)|=(4298492469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4298491639/10000000000 : ℝ)|^8443 ≤ (16400439846783/50000000000000 : ℝ)^6395
        have hw : |(4298491639/10000000000 : ℝ)|=(4298491639/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1250_box_4 (p : ℝ) (hpa : (4221/1024 : ℝ) ≤ p) (hpb : p ≤ (8443/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1120555291/5000000000 : ℝ)*x 0 + (2641183759/5000000000 : ℝ)*x 1 + (5282367557/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1120555291/5000000000 : ℝ)^8443 ≤ (6940951839747/50000000000000 : ℝ)^6395 := by
    have hnat : (1120555291 : ℕ)^8443*50000000000000^6395 ≤ 6940951839747^6395*5000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1120555291 5000000000 6940951839747 50000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2641183759/5000000000 : ℝ)^8443 ≤ (43059047941281/100000000000000 : ℝ)^6395 := by
    have hnat : (2641183759 : ℕ)^8443*100000000000000^6395 ≤ 43059047941281^6395*5000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2641183759 5000000000 43059047941281 100000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5282367557/10000000000 : ℝ)^8443 ≤ (21529524180499/50000000000000 : ℝ)^6395 := by
    have hnat : (5282367557 : ℕ)^8443*50000000000000^6395 ≤ 21529524180499^6395*10000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5282367557 10000000000 21529524180499 50000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8443/2048 : ℝ)) 8443 6395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1120555291/5000000000 : ℝ), (2641183759/5000000000 : ℝ), (5282367557/10000000000 : ℝ)] ![(6940951839747/50000000000000 : ℝ), (43059047941281/100000000000000 : ℝ), (21529524180499/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1120555291/5000000000 : ℝ)|^8443 ≤ (6940951839747/50000000000000 : ℝ)^6395
        have hw : |(-1120555291/5000000000 : ℝ)|=(1120555291/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2641183759/5000000000 : ℝ)|^8443 ≤ (43059047941281/100000000000000 : ℝ)^6395
        have hw : |(2641183759/5000000000 : ℝ)|=(2641183759/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5282367557/10000000000 : ℝ)|^8443 ≤ (21529524180499/50000000000000 : ℝ)^6395
        have hw : |(5282367557/10000000000 : ℝ)|=(5282367557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1250_box_5 (p : ℝ) (hpa : (4221/1024 : ℝ) ≤ p) (hpb : p ≤ (8443/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5361941971/10000000000 : ℝ)*x 0 + (-427066441/2000000000 : ℝ)*x 1 + (5282367473/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5361941971/10000000000 : ℝ)^8443 ≤ (43917485062327/100000000000000 : ℝ)^6395 := by
    have hnat : (5361941971 : ℕ)^8443*100000000000000^6395 ≤ 43917485062327^6395*10000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5361941971 10000000000 43917485062327 100000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (427066441/2000000000 : ℝ)^8443 ≤ (13023467465941/100000000000000 : ℝ)^6395 := by
    have hnat : (427066441 : ℕ)^8443*100000000000000^6395 ≤ 13023467465941^6395*2000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      427066441 2000000000 13023467465941 100000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5282367473/10000000000 : ℝ)^8443 ≤ (1345595233031/3125000000000 : ℝ)^6395 := by
    have hnat : (5282367473 : ℕ)^8443*3125000000000^6395 ≤ 1345595233031^6395*10000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5282367473 10000000000 1345595233031 3125000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8443/2048 : ℝ)) 8443 6395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5361941971/10000000000 : ℝ), (-427066441/2000000000 : ℝ), (5282367473/10000000000 : ℝ)] ![(43917485062327/100000000000000 : ℝ), (13023467465941/100000000000000 : ℝ), (1345595233031/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5361941971/10000000000 : ℝ)|^8443 ≤ (43917485062327/100000000000000 : ℝ)^6395
        have hw : |(5361941971/10000000000 : ℝ)|=(5361941971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-427066441/2000000000 : ℝ)|^8443 ≤ (13023467465941/100000000000000 : ℝ)^6395
        have hw : |(-427066441/2000000000 : ℝ)|=(427066441/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5282367473/10000000000 : ℝ)|^8443 ≤ (1345595233031/3125000000000 : ℝ)^6395
        have hw : |(5282367473/10000000000 : ℝ)|=(5282367473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1250_box_6 (p : ℝ) (hpa : (4221/1024 : ℝ) ≤ p) (hpb : p ≤ (8443/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1072388391/2000000000 : ℝ)*x 0 + (2641183751/5000000000 : ℝ)*x 1 + (-533833047/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1072388391/2000000000 : ℝ)^8443 ≤ (43917484889309/100000000000000 : ℝ)^6395 := by
    have hnat : (1072388391 : ℕ)^8443*100000000000000^6395 ≤ 43917484889309^6395*2000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1072388391 2000000000 43917484889309 100000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2641183751/5000000000 : ℝ)^8443 ≤ (4305904776909/10000000000000 : ℝ)^6395 := by
    have hnat : (2641183751 : ℕ)^8443*10000000000000^6395 ≤ 4305904776909^6395*5000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2641183751 5000000000 4305904776909 10000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (533833047/2500000000 : ℝ)^8443 ≤ (13023467329053/100000000000000 : ℝ)^6395 := by
    have hnat : (533833047 : ℕ)^8443*100000000000000^6395 ≤ 13023467329053^6395*2500000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      533833047 2500000000 13023467329053 100000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8443/2048 : ℝ)) 8443 6395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1072388391/2000000000 : ℝ), (2641183751/5000000000 : ℝ), (-533833047/2500000000 : ℝ)] ![(43917484889309/100000000000000 : ℝ), (4305904776909/10000000000000 : ℝ), (13023467329053/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1072388391/2000000000 : ℝ)|^8443 ≤ (43917484889309/100000000000000 : ℝ)^6395
        have hw : |(1072388391/2000000000 : ℝ)|=(1072388391/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2641183751/5000000000 : ℝ)|^8443 ≤ (4305904776909/10000000000000 : ℝ)^6395
        have hw : |(2641183751/5000000000 : ℝ)|=(2641183751/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-533833047/2500000000 : ℝ)|^8443 ≤ (13023467329053/100000000000000 : ℝ)^6395
        have hw : |(-533833047/2500000000 : ℝ)|=(533833047/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1250_box_7 (p : ℝ) (hpa : (4221/1024 : ℝ) ≤ p) (hpb : p ≤ (8443/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1060706619/2500000000 : ℝ)*x 0 + (4405122163/10000000000 : ℝ)*x 1 + (4405122193/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1060706619/2500000000 : ℝ)^8443 ≤ (6448248910747/20000000000000 : ℝ)^6395 := by
    have hnat : (1060706619 : ℕ)^8443*20000000000000^6395 ≤ 6448248910747^6395*2500000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1060706619 2500000000 6448248910747 20000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4405122163/10000000000 : ℝ)^8443 ≤ (33879377566309/100000000000000 : ℝ)^6395 := by
    have hnat : (4405122163 : ℕ)^8443*100000000000000^6395 ≤ 33879377566309^6395*10000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4405122163 10000000000 33879377566309 100000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4405122193/10000000000 : ℝ)^8443 ≤ (33879377870927/100000000000000 : ℝ)^6395 := by
    have hnat : (4405122193 : ℕ)^8443*100000000000000^6395 ≤ 33879377870927^6395*10000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4405122193 10000000000 33879377870927 100000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8443/2048 : ℝ)) 8443 6395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1060706619/2500000000 : ℝ), (4405122163/10000000000 : ℝ), (4405122193/10000000000 : ℝ)] ![(6448248910747/20000000000000 : ℝ), (33879377566309/100000000000000 : ℝ), (33879377870927/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1060706619/2500000000 : ℝ)|^8443 ≤ (6448248910747/20000000000000 : ℝ)^6395
        have hw : |(1060706619/2500000000 : ℝ)|=(1060706619/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4405122163/10000000000 : ℝ)|^8443 ≤ (33879377566309/100000000000000 : ℝ)^6395
        have hw : |(4405122163/10000000000 : ℝ)|=(4405122163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4405122193/10000000000 : ℝ)|^8443 ≤ (33879377870927/100000000000000 : ℝ)^6395
        have hw : |(4405122193/10000000000 : ℝ)|=(4405122193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1250_box_8 (p : ℝ) (hpa : (4221/1024 : ℝ) ≤ p) (hpb : p ≤ (8443/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-547269579/2500000000 : ℝ)*x 0 + (5219358187/10000000000 : ℝ)*x 1 + (5384333367/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (547269579/2500000000 : ℝ)^8443 ≤ (13457979150491/100000000000000 : ℝ)^6395 := by
    have hnat : (547269579 : ℕ)^8443*100000000000000^6395 ≤ 13457979150491^6395*2500000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      547269579 2500000000 13457979150491 100000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5219358187/10000000000 : ℝ)^8443 ≤ (42382241690973/100000000000000 : ℝ)^6395 := by
    have hnat : (5219358187 : ℕ)^8443*100000000000000^6395 ≤ 42382241690973^6395*10000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5219358187 10000000000 42382241690973 100000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5384333367/10000000000 : ℝ)^8443 ≤ (44159779138797/100000000000000 : ℝ)^6395 := by
    have hnat : (5384333367 : ℕ)^8443*100000000000000^6395 ≤ 44159779138797^6395*10000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5384333367 10000000000 44159779138797 100000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8443/2048 : ℝ)) 8443 6395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-547269579/2500000000 : ℝ), (5219358187/10000000000 : ℝ), (5384333367/10000000000 : ℝ)] ![(13457979150491/100000000000000 : ℝ), (42382241690973/100000000000000 : ℝ), (44159779138797/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-547269579/2500000000 : ℝ)|^8443 ≤ (13457979150491/100000000000000 : ℝ)^6395
        have hw : |(-547269579/2500000000 : ℝ)|=(547269579/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5219358187/10000000000 : ℝ)|^8443 ≤ (42382241690973/100000000000000 : ℝ)^6395
        have hw : |(5219358187/10000000000 : ℝ)|=(5219358187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5384333367/10000000000 : ℝ)|^8443 ≤ (44159779138797/100000000000000 : ℝ)^6395
        have hw : |(5384333367/10000000000 : ℝ)|=(5384333367/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1250_box_9 (p : ℝ) (hpa : (4221/1024 : ℝ) ≤ p) (hpb : p ≤ (8443/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2645036531/5000000000 : ℝ)*x 0 + (-2094817789/10000000000 : ℝ)*x 1 + (5384333007/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2645036531/5000000000 : ℝ)^8443 ≤ (43141994190319/100000000000000 : ℝ)^6395 := by
    have hnat : (2645036531 : ℕ)^8443*100000000000000^6395 ≤ 43141994190319^6395*5000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2645036531 5000000000 43141994190319 100000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2094817789/10000000000 : ℝ)^8443 ≤ (12698230557239/100000000000000 : ℝ)^6395 := by
    have hnat : (2094817789 : ℕ)^8443*100000000000000^6395 ≤ 12698230557239^6395*10000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2094817789 10000000000 12698230557239 100000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5384333007/10000000000 : ℝ)^8443 ≤ (4415977524069/10000000000000 : ℝ)^6395 := by
    have hnat : (5384333007 : ℕ)^8443*10000000000000^6395 ≤ 4415977524069^6395*10000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5384333007 10000000000 4415977524069 10000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8443/2048 : ℝ)) 8443 6395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2645036531/5000000000 : ℝ), (-2094817789/10000000000 : ℝ), (5384333007/10000000000 : ℝ)] ![(43141994190319/100000000000000 : ℝ), (12698230557239/100000000000000 : ℝ), (4415977524069/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2645036531/5000000000 : ℝ)|^8443 ≤ (43141994190319/100000000000000 : ℝ)^6395
        have hw : |(2645036531/5000000000 : ℝ)|=(2645036531/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2094817789/10000000000 : ℝ)|^8443 ≤ (12698230557239/100000000000000 : ℝ)^6395
        have hw : |(-2094817789/10000000000 : ℝ)|=(2094817789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5384333007/10000000000 : ℝ)|^8443 ≤ (4415977524069/10000000000000 : ℝ)^6395
        have hw : |(5384333007/10000000000 : ℝ)|=(5384333007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1250_box_10 (p : ℝ) (hpa : (4221/1024 : ℝ) ≤ p) (hpb : p ≤ (8443/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5290072791/10000000000 : ℝ)*x 0 + (5384333603/10000000000 : ℝ)*x 1 + (-2094817347/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5290072791/10000000000 : ℝ)^8443 ≤ (43141991272461/100000000000000 : ℝ)^6395 := by
    have hnat : (5290072791 : ℕ)^8443*100000000000000^6395 ≤ 43141991272461^6395*10000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5290072791 10000000000 43141991272461 100000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5384333603/10000000000 : ℝ)^8443 ≤ (22079890847111/50000000000000 : ℝ)^6395 := by
    have hnat : (5384333603 : ℕ)^8443*50000000000000^6395 ≤ 22079890847111^6395*10000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5384333603 10000000000 22079890847111 50000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2094817347/10000000000 : ℝ)^8443 ≤ (1269822701991/10000000000000 : ℝ)^6395 := by
    have hnat : (2094817347 : ℕ)^8443*10000000000000^6395 ≤ 1269822701991^6395*10000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2094817347 10000000000 1269822701991 10000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8443/2048 : ℝ)) 8443 6395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5290072791/10000000000 : ℝ), (5384333603/10000000000 : ℝ), (-2094817347/10000000000 : ℝ)] ![(43141991272461/100000000000000 : ℝ), (22079890847111/50000000000000 : ℝ), (1269822701991/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5290072791/10000000000 : ℝ)|^8443 ≤ (43141991272461/100000000000000 : ℝ)^6395
        have hw : |(5290072791/10000000000 : ℝ)|=(5290072791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5384333603/10000000000 : ℝ)|^8443 ≤ (22079890847111/50000000000000 : ℝ)^6395
        have hw : |(5384333603/10000000000 : ℝ)|=(5384333603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2094817347/10000000000 : ℝ)|^8443 ≤ (1269822701991/10000000000000 : ℝ)^6395
        have hw : |(-2094817347/10000000000 : ℝ)|=(2094817347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1250_box_11 (p : ℝ) (hpa : (4221/1024 : ℝ) ≤ p) (hpb : p ≤ (8443/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4478056269/10000000000 : ℝ)*x 0 + (1071846681/2500000000 : ℝ)*x 1 + (267961679/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4478056269/10000000000 : ℝ)^8443 ≤ (6924380124201/20000000000000 : ℝ)^6395 := by
    have hnat : (4478056269 : ℕ)^8443*20000000000000^6395 ≤ 6924380124201^6395*10000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4478056269 10000000000 6924380124201 20000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1071846681/2500000000 : ℝ)^8443 ≤ (32689048982803/100000000000000 : ℝ)^6395 := by
    have hnat : (1071846681 : ℕ)^8443*100000000000000^6395 ≤ 32689048982803^6395*2500000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1071846681 2500000000 32689048982803 100000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (267961679/625000000 : ℝ)^8443 ≤ (4086131299009/12500000000000 : ℝ)^6395 := by
    have hnat : (267961679 : ℕ)^8443*12500000000000^6395 ≤ 4086131299009^6395*625000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267961679 625000000 4086131299009 12500000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8443/2048 : ℝ)) 8443 6395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4478056269/10000000000 : ℝ), (1071846681/2500000000 : ℝ), (267961679/625000000 : ℝ)] ![(6924380124201/20000000000000 : ℝ), (32689048982803/100000000000000 : ℝ), (4086131299009/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4478056269/10000000000 : ℝ)|^8443 ≤ (6924380124201/20000000000000 : ℝ)^6395
        have hw : |(4478056269/10000000000 : ℝ)|=(4478056269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1071846681/2500000000 : ℝ)|^8443 ≤ (32689048982803/100000000000000 : ℝ)^6395
        have hw : |(1071846681/2500000000 : ℝ)|=(1071846681/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(267961679/625000000 : ℝ)|^8443 ≤ (4086131299009/12500000000000 : ℝ)^6395
        have hw : |(267961679/625000000 : ℝ)|=(267961679/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1250_box_12 (p : ℝ) (hpa : (4221/1024 : ℝ) ≤ p) (hpb : p ≤ (8443/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-204513091/1000000000 : ℝ)*x 0 + (43492211/80000000 : ℝ)*x 1 + (1054857109/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (204513091/1000000000 : ℝ)^8443 ≤ (6151052284907/50000000000000 : ℝ)^6395 := by
    have hnat : (204513091 : ℕ)^8443*50000000000000^6395 ≤ 6151052284907^6395*1000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      204513091 1000000000 6151052284907 50000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (43492211/80000000 : ℝ)^8443 ≤ (44725804152251/100000000000000 : ℝ)^6395 := by
    have hnat : (43492211 : ℕ)^8443*100000000000000^6395 ≤ 44725804152251^6395*80000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      43492211 80000000 44725804152251 100000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1054857109/2000000000 : ℝ)^8443 ≤ (21486045625907/50000000000000 : ℝ)^6395 := by
    have hnat : (1054857109 : ℕ)^8443*50000000000000^6395 ≤ 21486045625907^6395*2000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1054857109 2000000000 21486045625907 50000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8443/2048 : ℝ)) 8443 6395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-204513091/1000000000 : ℝ), (43492211/80000000 : ℝ), (1054857109/2000000000 : ℝ)] ![(6151052284907/50000000000000 : ℝ), (44725804152251/100000000000000 : ℝ), (21486045625907/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-204513091/1000000000 : ℝ)|^8443 ≤ (6151052284907/50000000000000 : ℝ)^6395
        have hw : |(-204513091/1000000000 : ℝ)|=(204513091/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(43492211/80000000 : ℝ)|^8443 ≤ (44725804152251/100000000000000 : ℝ)^6395
        have hw : |(43492211/80000000 : ℝ)|=(43492211/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1054857109/2000000000 : ℝ)|^8443 ≤ (21486045625907/50000000000000 : ℝ)^6395
        have hw : |(1054857109/2000000000 : ℝ)|=(1054857109/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1250_box_13 (p : ℝ) (hpa : (4221/1024 : ℝ) ≤ p) (hpb : p ≤ (8443/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2683818289/5000000000 : ℝ)*x 0 + (-427696437/2000000000 : ℝ)*x 1 + (5274285167/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2683818289/5000000000 : ℝ)^8443 ≤ (43979074917471/100000000000000 : ℝ)^6395 := by
    have hnat : (2683818289 : ℕ)^8443*100000000000000^6395 ≤ 43979074917471^6395*5000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2683818289 5000000000 43979074917471 100000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (427696437/2000000000 : ℝ)^8443 ≤ (13048837891689/100000000000000 : ℝ)^6395 := by
    have hnat : (427696437 : ℕ)^8443*100000000000000^6395 ≤ 13048837891689^6395*2000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      427696437 2000000000 13048837891689 100000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5274285167/10000000000 : ℝ)^8443 ≤ (42972087185781/100000000000000 : ℝ)^6395 := by
    have hnat : (5274285167 : ℕ)^8443*100000000000000^6395 ≤ 42972087185781^6395*10000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5274285167 10000000000 42972087185781 100000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8443/2048 : ℝ)) 8443 6395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2683818289/5000000000 : ℝ), (-427696437/2000000000 : ℝ), (5274285167/10000000000 : ℝ)] ![(43979074917471/100000000000000 : ℝ), (13048837891689/100000000000000 : ℝ), (42972087185781/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2683818289/5000000000 : ℝ)|^8443 ≤ (43979074917471/100000000000000 : ℝ)^6395
        have hw : |(2683818289/5000000000 : ℝ)|=(2683818289/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-427696437/2000000000 : ℝ)|^8443 ≤ (13048837891689/100000000000000 : ℝ)^6395
        have hw : |(-427696437/2000000000 : ℝ)|=(427696437/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5274285167/10000000000 : ℝ)|^8443 ≤ (42972087185781/100000000000000 : ℝ)^6395
        have hw : |(5274285167/10000000000 : ℝ)|=(5274285167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1250_box_14 (p : ℝ) (hpa : (4221/1024 : ℝ) ≤ p) (hpb : p ≤ (8443/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5367636501/10000000000 : ℝ)*x 0 + (13185713/25000000 : ℝ)*x 1 + (-2138482243/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5367636501/10000000000 : ℝ)^8443 ≤ (43979074084539/100000000000000 : ℝ)^6395 := by
    have hnat : (5367636501 : ℕ)^8443*100000000000000^6395 ≤ 43979074084539^6395*10000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5367636501 10000000000 43979074084539 100000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (13185713/25000000 : ℝ)^8443 ≤ (2685755471297/6250000000000 : ℝ)^6395 := by
    have hnat : (13185713 : ℕ)^8443*6250000000000^6395 ≤ 2685755471297^6395*25000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13185713 25000000 2685755471297 6250000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2138482243/10000000000 : ℝ)^8443 ≤ (652441917947/5000000000000 : ℝ)^6395 := by
    have hnat : (2138482243 : ℕ)^8443*5000000000000^6395 ≤ 652441917947^6395*10000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2138482243 10000000000 652441917947 5000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8443/2048 : ℝ)) 8443 6395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5367636501/10000000000 : ℝ), (13185713/25000000 : ℝ), (-2138482243/10000000000 : ℝ)] ![(43979074084539/100000000000000 : ℝ), (2685755471297/6250000000000 : ℝ), (652441917947/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5367636501/10000000000 : ℝ)|^8443 ≤ (43979074084539/100000000000000 : ℝ)^6395
        have hw : |(5367636501/10000000000 : ℝ)|=(5367636501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(13185713/25000000 : ℝ)|^8443 ≤ (2685755471297/6250000000000 : ℝ)^6395
        have hw : |(13185713/25000000 : ℝ)|=(13185713/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2138482243/10000000000 : ℝ)|^8443 ≤ (652441917947/5000000000000 : ℝ)^6395
        have hw : |(-2138482243/10000000000 : ℝ)|=(2138482243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1250_box_15 (p : ℝ) (hpa : (4221/1024 : ℝ) ≤ p) (hpb : p ≤ (8443/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4223927743/10000000000 : ℝ)*x 0 + (4414448747/10000000000 : ℝ)*x 1 + (882889771/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4223927743/10000000000 : ℝ)^8443 ≤ (8012944203261/25000000000000 : ℝ)^6395 := by
    have hnat : (4223927743 : ℕ)^8443*25000000000000^6395 ≤ 8012944203261^6395*10000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4223927743 10000000000 8012944203261 25000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4414448747/10000000000 : ℝ)^8443 ≤ (265422742481/781250000000 : ℝ)^6395 := by
    have hnat : (4414448747 : ℕ)^8443*781250000000^6395 ≤ 265422742481^6395*10000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4414448747 10000000000 265422742481 781250000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (882889771/2000000000 : ℝ)^8443 ≤ (6794822426987/20000000000000 : ℝ)^6395 := by
    have hnat : (882889771 : ℕ)^8443*20000000000000^6395 ≤ 6794822426987^6395*2000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      882889771 2000000000 6794822426987 20000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8443/2048 : ℝ)) 8443 6395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4223927743/10000000000 : ℝ), (4414448747/10000000000 : ℝ), (882889771/2000000000 : ℝ)] ![(8012944203261/25000000000000 : ℝ), (265422742481/781250000000 : ℝ), (6794822426987/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4223927743/10000000000 : ℝ)|^8443 ≤ (8012944203261/25000000000000 : ℝ)^6395
        have hw : |(4223927743/10000000000 : ℝ)|=(4223927743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4414448747/10000000000 : ℝ)|^8443 ≤ (265422742481/781250000000 : ℝ)^6395
        have hw : |(4414448747/10000000000 : ℝ)|=(4414448747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(882889771/2000000000 : ℝ)|^8443 ≤ (6794822426987/20000000000000 : ℝ)^6395
        have hw : |(882889771/2000000000 : ℝ)|=(882889771/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1250_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4221/1024 : ℝ) ≤ p) (hpb : p ≤ (8443/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151585227/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3527/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11489/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(7781/12500 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(7423/12500 : ℝ) ∧ (20033/25000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (83363/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3527/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11489/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3527/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11489/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3527/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11489/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3527/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11489/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3527/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11489/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3527/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11489/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11489/100000 : ℝ) ^ (4221/1024 : ℝ) ≤ (1672350440260793/12500000000000000000 : ℝ) := by
    have hpowers : (11489/100000 : ℝ)^4221 ≤ (1672350440260793/12500000000000000000 : ℝ)^1024 := by
      have hnat : (11489 : ℕ)^4221*12500000000000000000^1024 ≤ 1672350440260793^1024*100000^4221 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11489 100000 1672350440260793 12500000000000000000 4221 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11489/100000 : ℝ)) (X := (1672350440260793/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4221 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3527/25000 : ℝ) ^ (4221/1024 : ℝ) ≤ (1949471107982493/6250000000000000000 : ℝ) := by
    have hpowers : (3527/25000 : ℝ)^4221 ≤ (1949471107982493/6250000000000000000 : ℝ)^1024 := by
      have hnat : (3527 : ℕ)^4221*6250000000000000000^1024 ≤ 1949471107982493^1024*25000^4221 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3527 25000 1949471107982493 6250000000000000000 4221 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3527/25000 : ℝ)) (X := (1949471107982493/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 4221 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (6251672350440260793/6250000000000000000 : ℝ) ≤ (10000649064524663/10000000000000000 : ℝ) ^ (4221/1024 : ℝ) := by
    have hpowers : (6251672350440260793/6250000000000000000 : ℝ)^1024 ≤ (10000649064524663/10000000000000000 : ℝ)^4221 := by
      have hnat : (6251672350440260793 : ℕ)^1024*10000000000000000^4221 ≤ 10000649064524663^4221*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6251672350440260793 6250000000000000000 10000649064524663 10000000000000000 1024 4221 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000649064524663/10000000000000000 : ℝ)) (X := (6251672350440260793/6250000000000000000 : ℝ)) (by norm_num) 4221 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (12505571292656225779/12500000000000000000 : ℝ) ≤ (10001081078605341/10000000000000000 : ℝ) ^ (4221/1024 : ℝ) := by
    have hpowers : (12505571292656225779/12500000000000000000 : ℝ)^1024 ≤ (10001081078605341/10000000000000000 : ℝ)^4221 := by
      have hnat : (12505571292656225779 : ℕ)^1024*10000000000000000^4221 ≤ 10001081078605341^4221*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12505571292656225779 12500000000000000000 10001081078605341 10000000000000000 1024 4221 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001081078605341/10000000000000000 : ℝ)) (X := (12505571292656225779/12500000000000000000 : ℝ)) (by norm_num) 4221 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (3126949471107982493/3125000000000000000 : ℝ) ≤ (10001513092686019/10000000000000000 : ℝ) ^ (4221/1024 : ℝ) := by
    have hpowers : (3126949471107982493/3125000000000000000 : ℝ)^1024 ≤ (10001513092686019/10000000000000000 : ℝ)^4221 := by
      have hnat : (3126949471107982493 : ℕ)^1024*10000000000000000^4221 ≤ 10001513092686019^4221*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3126949471107982493 3125000000000000000 10001513092686019 10000000000000000 1024 4221 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001513092686019/10000000000000000 : ℝ)) (X := (3126949471107982493/3125000000000000000 : ℝ)) (by norm_num) 4221 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1672350440260793/12500000000000000000 : ℝ) ≤ ((26181773080444273313/26190000000000000000 : ℝ)+2*(216007040339/130950000000000 : ℝ)*(11489/100000 : ℝ))^(4221/1024 : ℝ) := by
    rw [show (26181773080444273313/26190000000000000000 : ℝ)+2*(216007040339/130950000000000 : ℝ)*(11489/100000 : ℝ)=(10000649064524663/10000000000000000 : ℝ) by norm_num, show 1+2*(1672350440260793/12500000000000000000 : ℝ)=(6251672350440260793/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1949471107982493/6250000000000000000 : ℝ)+(1672350440260793/12500000000000000000 : ℝ) ≤ ((26181773080444273313/26190000000000000000 : ℝ)+(216007040339/130950000000000 : ℝ)*((3527/25000 : ℝ)+(11489/100000 : ℝ)))^(4221/1024 : ℝ) := by
    rw [show (26181773080444273313/26190000000000000000 : ℝ)+(216007040339/130950000000000 : ℝ)*((3527/25000 : ℝ)+(11489/100000 : ℝ))=(10001081078605341/10000000000000000 : ℝ) by norm_num, show 1+(1949471107982493/6250000000000000000 : ℝ)+(1672350440260793/12500000000000000000 : ℝ)=(12505571292656225779/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1949471107982493/6250000000000000000 : ℝ) ≤ ((26181773080444273313/26190000000000000000 : ℝ)+2*(216007040339/130950000000000 : ℝ)*(3527/25000 : ℝ))^(4221/1024 : ℝ) := by
    rw [show (26181773080444273313/26190000000000000000 : ℝ)+2*(216007040339/130950000000000 : ℝ)*(3527/25000 : ℝ)=(10001513092686019/10000000000000000 : ℝ) by norm_num, show 1+2*(1949471107982493/6250000000000000000 : ℝ)=(3126949471107982493/3125000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (26181773080444273313/26190000000000000000 : ℝ)*(X 1 0+X 2 0)+(216007040339/130950000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4221/1024 : ℝ)) (lo := (11489/100000 : ℝ)) (hi := (3527/25000 : ℝ)) (c := (26181773080444273313/26190000000000000000 : ℝ)) (alpha := (216007040339/130950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (26181773080444273313/26190000000000000000 : ℝ)*(X 0 1+X 2 1)+(216007040339/130950000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4221/1024 : ℝ)) (lo := (11489/100000 : ℝ)) (hi := (3527/25000 : ℝ)) (c := (26181773080444273313/26190000000000000000 : ℝ)) (alpha := (216007040339/130950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (26181773080444273313/26190000000000000000 : ℝ)*(X 0 2+X 1 2)+(216007040339/130950000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4221/1024 : ℝ)) (lo := (11489/100000 : ℝ)) (hi := (3527/25000 : ℝ)) (c := (26181773080444273313/26190000000000000000 : ℝ)) (alpha := (216007040339/130950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1992843499/10000000000 : ℝ)*X 0 0+(1343680047/2500000000 : ℝ)*X 0 1+(5374720559/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1250_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1324212703/2500000000 : ℝ)*X 1 0+(-2098698741/10000000000 : ℝ)*X 1 1+(2687360049/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1250_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5296850723/10000000000 : ℝ)*X 2 0+(5374720689/10000000000 : ℝ)*X 2 1+(-2098698061/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1250_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4456126803/10000000000 : ℝ)*X 0 0+(4298492469/10000000000 : ℝ)*X 0 1+(4298491639/10000000000 : ℝ)*X 0 2+(4456126803/10000000000 : ℝ)*X 1 0+(4298492469/10000000000 : ℝ)*X 1 1+(4298491639/10000000000 : ℝ)*X 1 2+(4456126803/10000000000 : ℝ)*X 2 0+(4298492469/10000000000 : ℝ)*X 2 1+(4298491639/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1250_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1120555291/5000000000 : ℝ)*X 0 0+(2641183759/5000000000 : ℝ)*X 0 1+(5282367557/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1250_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5361941971/10000000000 : ℝ)*X 1 0+(-427066441/2000000000 : ℝ)*X 1 1+(5282367473/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1250_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1072388391/2000000000 : ℝ)*X 2 0+(2641183751/5000000000 : ℝ)*X 2 1+(-533833047/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1250_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1060706619/2500000000 : ℝ)*X 0 0+(4405122163/10000000000 : ℝ)*X 0 1+(4405122193/10000000000 : ℝ)*X 0 2+(1060706619/2500000000 : ℝ)*X 1 0+(4405122163/10000000000 : ℝ)*X 1 1+(4405122193/10000000000 : ℝ)*X 1 2+(1060706619/2500000000 : ℝ)*X 2 0+(4405122163/10000000000 : ℝ)*X 2 1+(4405122193/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1250_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-547269579/2500000000 : ℝ)*X 0 0+(5219358187/10000000000 : ℝ)*X 0 1+(5384333367/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1250_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((2645036531/5000000000 : ℝ)*X 1 0+(-2094817789/10000000000 : ℝ)*X 1 1+(5384333007/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1250_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5290072791/10000000000 : ℝ)*X 2 0+(5384333603/10000000000 : ℝ)*X 2 1+(-2094817347/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1250_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4478056269/10000000000 : ℝ)*X 0 0+(1071846681/2500000000 : ℝ)*X 0 1+(267961679/625000000 : ℝ)*X 0 2+(4478056269/10000000000 : ℝ)*X 1 0+(1071846681/2500000000 : ℝ)*X 1 1+(267961679/625000000 : ℝ)*X 1 2+(4478056269/10000000000 : ℝ)*X 2 0+(1071846681/2500000000 : ℝ)*X 2 1+(267961679/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1250_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-204513091/1000000000 : ℝ)*X 0 0+(43492211/80000000 : ℝ)*X 0 1+(1054857109/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1250_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((2683818289/5000000000 : ℝ)*X 1 0+(-427696437/2000000000 : ℝ)*X 1 1+(5274285167/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1250_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5367636501/10000000000 : ℝ)*X 2 0+(13185713/25000000 : ℝ)*X 2 1+(-2138482243/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1250_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((4223927743/10000000000 : ℝ)*X 0 0+(4414448747/10000000000 : ℝ)*X 0 1+(882889771/2000000000 : ℝ)*X 0 2+(4223927743/10000000000 : ℝ)*X 1 0+(4414448747/10000000000 : ℝ)*X 1 1+(882889771/2000000000 : ℝ)*X 1 2+(4223927743/10000000000 : ℝ)*X 2 0+(4414448747/10000000000 : ℝ)*X 2 1+(882889771/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1250_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-7781/12500 : ℝ) ≤ (-271702400752808416800107553985943/436500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (611339/6250000000000 : ℝ)*(lower0) + (21763839/100000000000000 : ℝ)*(lower2) + (13439129/50000000000000 : ℝ)*(lower3) + (6075371/20000000000000 : ℝ)*(lower4) + (4009808817571511/100000000000000 : ℝ)*(major0) + (4009808817571511/100000000000000 : ℝ)*(major1) + (4009808817571511/100000000000000 : ℝ)*(major2) + (499193007/25000000000000 : ℝ)*(sp1) + (1993824937/100000000000000 : ℝ)*(sp2) + (5395115799669313/100000000000000 : ℝ)*(sp4) + (1079022760579457/20000000000000 : ℝ)*(sp5) + (674389225730547/12500000000000 : ℝ)*(sp6) + (661311005332391/25000000000000 : ℝ)*(sp7) + (6374720911/100000000000000 : ℝ)*(sp15) + (105810015842019/4000000000000 : ℝ)*(f.failure) + (5395115799669313/100000000000000 : ℝ)*(f.sum) + (51266650625213/13095000000000000000000000000 : ℝ)*base65 + (1273727483041687327/291000000000000000000000000000000 : ℝ)*base67 + (1276319634823312673/291000000000000000000000000000000 : ℝ)*base70 + (1044249087433312673/291000000000000000000000000000000 : ℝ)*base72 + (11661857387381/6547500000000000000000000000 : ℝ)*base74 + (1301896363648687327/291000000000000000000000000000000 : ℝ)*base75 + (1509293646106687327/291000000000000000000000000000000 : ℝ)*base77 + (2886648756640687327/291000000000000000000000000000000 : ℝ)*base79 + (4981863805909/6547500000000000000000000000 : ℝ)*base81 + (2253313/400000000000000000000 : ℝ)*base89 + (2253313/400000000000000000000 : ℝ)*base91 + (2253313/400000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (7423/12500 : ℝ) ≤ (450036904349937297052798914323/757812500000000000000000000000 : ℝ) := by norm_num
    linear_combination (4693187/25000000000000 : ℝ)*(upper1) + (11374169/100000000000000 : ℝ)*(upper2) + (89218017/50000000000000 : ℝ)*(upper3) + (181284747/50000000000000 : ℝ)*(upper4) + (116407663/100000000000000 : ℝ)*(upper5) + (127366478136747/3125000000000 : ℝ)*(major0) + (127366478136747/3125000000000 : ℝ)*(major1) + (127366478136747/3125000000000 : ℝ)*(major2) + (1088584536113999/20000000000000 : ℝ)*(sp0) + (5442495565301653/100000000000000 : ℝ)*(sp1) + (2721452879138799/50000000000000 : ℝ)*(sp2) + (1344368241232341/50000000000000 : ℝ)*(sp3) + (8461146199/50000000000000 : ℝ)*(sp6) + (427115268343/100000000000000 : ℝ)*(sp9) + (1344368241232341/50000000000000 : ℝ)*(f.failure) + (1088584536113999/20000000000000 : ℝ)*(f.sum) + (11629131414613/1455000000000000000000000000 : ℝ)*base65 + (19968921135491493/3031250000000000000000000000000 : ℝ)*base67 + (3774219190335243/3031250000000000000000000000000 : ℝ)*base69 + (91549860717946007/3031250000000000000000000000000 : ℝ)*base72 + (2567479879439/727500000000000000000000000 : ℝ)*base73 + (13705224114397743/3031250000000000000000000000000 : ℝ)*base75 + (97282236198383507/3031250000000000000000000000000 : ℝ)*base78 + (7725351494053993/3031250000000000000000000000000 : ℝ)*base79 + (11834053381489/181875000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (29773593/5000000000000000000000 : ℝ)*base90 + (29773593/5000000000000000000000 : ℝ)*base92 + (29773593/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (20033/25000 : ℝ) ≤ (77730908507946409561121129/97000000000000000000000000 : ℝ) := by norm_num
    linear_combination (281203857/100000000000000 : ℝ)*(lower3) + (82766889/100000000000000 : ℝ)*(upper4) + (28196423/25000000000000 : ℝ)*(lower5) + (181697561152287/4000000000000 : ℝ)*(major0) + (181697561152287/4000000000000 : ℝ)*(major1) + (181697561152287/4000000000000 : ℝ)*(major2) + (15172065571/100000000000000 : ℝ)*(sp0) + (40348316573/50000000000000 : ℝ)*(sp1) + (445163589487/100000000000000 : ℝ)*(sp2) + (90047125863/50000000000000 : ℝ)*(sp3) + (3030763703626679/50000000000000 : ℝ)*(sp8) + (6061461882685783/100000000000000 : ℝ)*(sp9) + (3030548707864721/50000000000000 : ℝ)*(sp10) + (149822186581773/5000000000000 : ℝ)*(sp11) + (1498311912943593/50000000000000 : ℝ)*(f.failure) + (6061542579318929/100000000000000 : ℝ)*(f.sum) + (385979111257/873000000000000000000000000 : ℝ)*base65 + (69678951017790253/3880000000000000000000000000000 : ℝ)*base67 + (16877303814089747/3880000000000000000000000000000 : ℝ)*base70 + (5449318544350253/3880000000000000000000000000000 : ℝ)*base71 + (2490110861557/873000000000000000000000000 : ℝ)*base73 + (31247804204409747/3880000000000000000000000000000 : ℝ)*base76 + (10528791600649747/3880000000000000000000000000000 : ℝ)*base78 + (49406545530790253/3880000000000000000000000000000 : ℝ)*base79 + (2448399172981/873000000000000000000000000 : ℝ)*base81 + (33100611/5000000000000000000000 : ℝ)*base89 + (33100611/5000000000000000000000 : ℝ)*base91 + (33100611/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-83363/100000 : ℝ) ≤ (-22741834125864418097014083327959/27281250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (5311981/50000000000000 : ℝ)*(upper3) + (15150427/25000000000000 : ℝ)*(lower4) + (7381513/50000000000000 : ℝ)*(upper5) + (572248975311457/12500000000000 : ℝ)*(major0) + (572248975311457/12500000000000 : ℝ)*(major1) + (572248975311457/12500000000000 : ℝ)*(major2) + (3496248269/25000000000000 : ℝ)*(sp4) + (315397899373/100000000000000 : ℝ)*(sp5) + (84619556641/25000000000000 : ℝ)*(sp6) + (7392612317/5000000000000 : ℝ)*(sp7) + (1232735740507077/20000000000000 : ℝ)*(sp12) + (192605540300909/3125000000000 : ℝ)*(sp13) + (6163354209301897/100000000000000 : ℝ)*(sp14) + (3019929956847587/100000000000000 : ℝ)*(sp15) + (377509726136741/12500000000000 : ℝ)*(f.failure) + (6163692687528461/100000000000000 : ℝ)*(f.sum) + (33306813587137/13095000000000000000000000000 : ℝ)*base66 + (270626395629927449/36375000000000000000000000000000 : ℝ)*base67 + (572723978483822551/36375000000000000000000000000000 : ℝ)*base70 + (256088237672072551/36375000000000000000000000000000 : ℝ)*base72 + (38211850308797/3273750000000000000000000000 : ℝ)*base73 + (454282866944822551/36375000000000000000000000000000 : ℝ)*base76 + (163258145330822551/36375000000000000000000000000000 : ℝ)*base78 + (89673900674447551/36375000000000000000000000000000 : ℝ)*base80 + (11325984997039/6547500000000000000000000000 : ℝ)*base81 + (17525207/1250000000000000000000 : ℝ)*base89 + (17525207/1250000000000000000000 : ℝ)*base91 + (17525207/1250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1250_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4221/1024 : ℝ) ≤ p) (hpb : p ≤ (8443/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151585227/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3527/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11489/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(7781/12500 : ℝ) ≤ X j i ∧ X j i ≤ -(7423/12500 : ℝ) else (20033/25000 : ℝ) ≤ X j i ∧ X j i ≤ (83363/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1250_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1250_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4221/1024 : ℝ) ≤ p) (hpb : p ≤ (8443/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151585227/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3527/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11489/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(7781/12500 : ℝ) ≤ X j i ∧ X j i ≤ -(7423/12500 : ℝ) else (20033/25000 : ℝ) ≤ X j i ∧ X j i ≤ (83363/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1250_box p A d hA hpa hpb X hX hsign hratio hlower
  exact h0
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4221/1024 : ℝ) ≤ p) (hpb : p ≤ (8443/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151585227/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3527/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11489/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(7781/12500 : ℝ) ≤ X j i ∧ X j i ≤ -(7423/12500 : ℝ) else (20033/25000 : ℝ) ≤ X j i ∧ X j i ≤ (83363/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1250_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
