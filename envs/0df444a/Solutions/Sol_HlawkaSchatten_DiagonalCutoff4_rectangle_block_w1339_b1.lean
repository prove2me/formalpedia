-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1339_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:03:33.505789+00:00
-- url     : https://prove2.me/submissions/236788bd-98d2-4676-b1fe-6e22ee118225

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
theorem support_rectangle_w1339_s3_0 (p : ℝ) (hpa : (2149/512 : ℝ) ≤ p) (hpb : p ≤ (4299/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-204477467/1000000000 : ℝ)*x 0 + (1356889003/2500000000 : ℝ)*x 1 + (130774941/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (204477467/1000000000 : ℝ)^4299 ≤ (2489623971033/20000000000000 : ℝ)^3275 := by
    have hnat : (204477467 : ℕ)^4299*20000000000000^3275 ≤ 2489623971033^3275*1000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      204477467 1000000000 2489623971033 20000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1356889003/2500000000 : ℝ)^4299 ≤ (44835557980941/100000000000000 : ℝ)^3275 := by
    have hnat : (1356889003 : ℕ)^4299*100000000000000^3275 ≤ 44835557980941^3275*2500000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1356889003 2500000000 44835557980941 100000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (130774941/250000000 : ℝ)^4299 ≤ (533954026899/1250000000000 : ℝ)^3275 := by
    have hnat : (130774941 : ℕ)^4299*1250000000000^3275 ≤ 533954026899^3275*250000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      130774941 250000000 533954026899 1250000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4299/1024 : ℝ)) 4299 3275 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-204477467/1000000000 : ℝ), (1356889003/2500000000 : ℝ), (130774941/250000000 : ℝ)] ![(2489623971033/20000000000000 : ℝ), (44835557980941/100000000000000 : ℝ), (533954026899/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-204477467/1000000000 : ℝ)|^4299 ≤ (2489623971033/20000000000000 : ℝ)^3275
        have hw : |(-204477467/1000000000 : ℝ)|=(204477467/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1356889003/2500000000 : ℝ)|^4299 ≤ (44835557980941/100000000000000 : ℝ)^3275
        have hw : |(1356889003/2500000000 : ℝ)|=(1356889003/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(130774941/250000000 : ℝ)|^4299 ≤ (533954026899/1250000000000 : ℝ)^3275
        have hw : |(130774941/250000000 : ℝ)|=(130774941/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1339_s3_1 (p : ℝ) (hpa : (2149/512 : ℝ) ≤ p) (hpb : p ≤ (4299/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5352795099/10000000000 : ℝ)*x 0 + (-1072619087/5000000000 : ℝ)*x 1 + (2615498859/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5352795099/10000000000 : ℝ)^4299 ≤ (44026630108349/100000000000000 : ℝ)^3275 := by
    have hnat : (5352795099 : ℕ)^4299*100000000000000^3275 ≤ 44026630108349^3275*10000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5352795099 10000000000 44026630108349 100000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1072619087/5000000000 : ℝ)^4299 ≤ (20714135773/156250000000 : ℝ)^3275 := by
    have hnat : (1072619087 : ℕ)^4299*156250000000^3275 ≤ 20714135773^3275*5000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1072619087 5000000000 20714135773 156250000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2615498859/5000000000 : ℝ)^4299 ≤ (5339540373503/12500000000000 : ℝ)^3275 := by
    have hnat : (2615498859 : ℕ)^4299*12500000000000^3275 ≤ 5339540373503^3275*5000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2615498859 5000000000 5339540373503 12500000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4299/1024 : ℝ)) 4299 3275 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5352795099/10000000000 : ℝ), (-1072619087/5000000000 : ℝ), (2615498859/5000000000 : ℝ)] ![(44026630108349/100000000000000 : ℝ), (20714135773/156250000000 : ℝ), (5339540373503/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5352795099/10000000000 : ℝ)|^4299 ≤ (44026630108349/100000000000000 : ℝ)^3275
        have hw : |(5352795099/10000000000 : ℝ)|=(5352795099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1072619087/5000000000 : ℝ)|^4299 ≤ (20714135773/156250000000 : ℝ)^3275
        have hw : |(-1072619087/5000000000 : ℝ)|=(1072619087/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2615498859/5000000000 : ℝ)|^4299 ≤ (5339540373503/12500000000000 : ℝ)^3275
        have hw : |(2615498859/5000000000 : ℝ)|=(2615498859/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1339_s3_2 (p : ℝ) (hpa : (2149/512 : ℝ) ≤ p) (hpb : p ≤ (4299/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (669099359/1250000000 : ℝ)*x 0 + (1046199603/2000000000 : ℝ)*x 1 + (-2145238083/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (669099359/1250000000 : ℝ)^4299 ≤ (22013313828749/50000000000000 : ℝ)^3275 := by
    have hnat : (669099359 : ℕ)^4299*50000000000000^3275 ≤ 22013313828749^3275*1250000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      669099359 1250000000 22013313828749 50000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1046199603/2000000000 : ℝ)^4299 ≤ (42716326171649/100000000000000 : ℝ)^3275 := by
    have hnat : (1046199603 : ℕ)^4299*100000000000000^3275 ≤ 42716326171649^3275*2000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1046199603 2000000000 42716326171649 100000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2145238083/10000000000 : ℝ)^4299 ≤ (13257046156529/100000000000000 : ℝ)^3275 := by
    have hnat : (2145238083 : ℕ)^4299*100000000000000^3275 ≤ 13257046156529^3275*10000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2145238083 10000000000 13257046156529 100000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4299/1024 : ℝ)) 4299 3275 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(669099359/1250000000 : ℝ), (1046199603/2000000000 : ℝ), (-2145238083/10000000000 : ℝ)] ![(22013313828749/50000000000000 : ℝ), (42716326171649/100000000000000 : ℝ), (13257046156529/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(669099359/1250000000 : ℝ)|^4299 ≤ (22013313828749/50000000000000 : ℝ)^3275
        have hw : |(669099359/1250000000 : ℝ)|=(669099359/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1046199603/2000000000 : ℝ)|^4299 ≤ (42716326171649/100000000000000 : ℝ)^3275
        have hw : |(1046199603/2000000000 : ℝ)|=(1046199603/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2145238083/10000000000 : ℝ)|^4299 ≤ (13257046156529/100000000000000 : ℝ)^3275
        have hw : |(-2145238083/10000000000 : ℝ)|=(2145238083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1339_s3_3 (p : ℝ) (hpa : (2149/512 : ℝ) ≤ p) (hpb : p ≤ (4299/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4326321087/10000000000 : ℝ)*x 0 + (4125271147/10000000000 : ℝ)*x 1 + (4536511917/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4326321087/10000000000 : ℝ)^4299 ≤ (8323066550501/25000000000000 : ℝ)^3275 := by
    have hnat : (4326321087 : ℕ)^4299*25000000000000^3275 ≤ 8323066550501^3275*10000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4326321087 10000000000 8323066550501 25000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4125271147/10000000000 : ℝ)^4299 ≤ (15638149526113/50000000000000 : ℝ)^3275 := by
    have hnat : (4125271147 : ℕ)^4299*50000000000000^3275 ≤ 15638149526113^3275*10000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4125271147 10000000000 15638149526113 50000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4536511917/10000000000 : ℝ)^4299 ≤ (35431434729931/100000000000000 : ℝ)^3275 := by
    have hnat : (4536511917 : ℕ)^4299*100000000000000^3275 ≤ 35431434729931^3275*10000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4536511917 10000000000 35431434729931 100000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4299/1024 : ℝ)) 4299 3275 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4326321087/10000000000 : ℝ), (4125271147/10000000000 : ℝ), (4536511917/10000000000 : ℝ)] ![(8323066550501/25000000000000 : ℝ), (15638149526113/50000000000000 : ℝ), (35431434729931/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4326321087/10000000000 : ℝ)|^4299 ≤ (8323066550501/25000000000000 : ℝ)^3275
        have hw : |(4326321087/10000000000 : ℝ)|=(4326321087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4125271147/10000000000 : ℝ)|^4299 ≤ (15638149526113/50000000000000 : ℝ)^3275
        have hw : |(4125271147/10000000000 : ℝ)|=(4125271147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4536511917/10000000000 : ℝ)|^4299 ≤ (35431434729931/100000000000000 : ℝ)^3275
        have hw : |(4536511917/10000000000 : ℝ)|=(4536511917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1339_s3_4 (p : ℝ) (hpa : (2149/512 : ℝ) ≤ p) (hpb : p ≤ (4299/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2044793971/10000000000 : ℝ)*x 0 + (2615909179/5000000000 : ℝ)*x 1 + (2713365221/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2044793971/10000000000 : ℝ)^4299 ≤ (3112068523603/25000000000000 : ℝ)^3275 := by
    have hnat : (2044793971 : ℕ)^4299*25000000000000^3275 ≤ 3112068523603^3275*10000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2044793971 10000000000 3112068523603 25000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2615909179/5000000000 : ℝ)^4299 ≤ (42725119870797/100000000000000 : ℝ)^3275 := by
    have hnat : (2615909179 : ℕ)^4299*100000000000000^3275 ≤ 42725119870797^3275*5000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2615909179 5000000000 42725119870797 100000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2713365221/5000000000 : ℝ)^4299 ≤ (44826606024079/100000000000000 : ℝ)^3275 := by
    have hnat : (2713365221 : ℕ)^4299*100000000000000^3275 ≤ 44826606024079^3275*5000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2713365221 5000000000 44826606024079 100000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4299/1024 : ℝ)) 4299 3275 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2044793971/10000000000 : ℝ), (2615909179/5000000000 : ℝ), (2713365221/5000000000 : ℝ)] ![(3112068523603/25000000000000 : ℝ), (42725119870797/100000000000000 : ℝ), (44826606024079/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2044793971/10000000000 : ℝ)|^4299 ≤ (3112068523603/25000000000000 : ℝ)^3275
        have hw : |(-2044793971/10000000000 : ℝ)|=(2044793971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2615909179/5000000000 : ℝ)|^4299 ≤ (42725119870797/100000000000000 : ℝ)^3275
        have hw : |(2615909179/5000000000 : ℝ)|=(2615909179/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2713365221/5000000000 : ℝ)|^4299 ≤ (44826606024079/100000000000000 : ℝ)^3275
        have hw : |(2713365221/5000000000 : ℝ)|=(2713365221/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1339_s3_5 (p : ℝ) (hpa : (2149/512 : ℝ) ≤ p) (hpb : p ≤ (4299/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5302182381/10000000000 : ℝ)*x 0 + (-1949505279/10000000000 : ℝ)*x 1 + (2713365219/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5302182381/10000000000 : ℝ)^4299 ≤ (10870247347267/25000000000000 : ℝ)^3275 := by
    have hnat : (5302182381 : ℕ)^4299*25000000000000^3275 ≤ 10870247347267^3275*10000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5302182381 10000000000 10870247347267 25000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1949505279/10000000000 : ℝ)^4299 ≤ (11692404619417/100000000000000 : ℝ)^3275 := by
    have hnat : (1949505279 : ℕ)^4299*100000000000000^3275 ≤ 11692404619417^3275*10000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1949505279 10000000000 11692404619417 100000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2713365219/5000000000 : ℝ)^4299 ≤ (44826605980707/100000000000000 : ℝ)^3275 := by
    have hnat : (2713365219 : ℕ)^4299*100000000000000^3275 ≤ 44826605980707^3275*5000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2713365219 5000000000 44826605980707 100000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4299/1024 : ℝ)) 4299 3275 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5302182381/10000000000 : ℝ), (-1949505279/10000000000 : ℝ), (2713365219/5000000000 : ℝ)] ![(10870247347267/25000000000000 : ℝ), (11692404619417/100000000000000 : ℝ), (44826605980707/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5302182381/10000000000 : ℝ)|^4299 ≤ (10870247347267/25000000000000 : ℝ)^3275
        have hw : |(5302182381/10000000000 : ℝ)|=(5302182381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1949505279/10000000000 : ℝ)|^4299 ≤ (11692404619417/100000000000000 : ℝ)^3275
        have hw : |(-1949505279/10000000000 : ℝ)|=(1949505279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2713365219/5000000000 : ℝ)|^4299 ≤ (44826605980707/100000000000000 : ℝ)^3275
        have hw : |(2713365219/5000000000 : ℝ)|=(2713365219/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1339_s3_6 (p : ℝ) (hpa : (2149/512 : ℝ) ≤ p) (hpb : p ≤ (4299/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5302182117/10000000000 : ℝ)*x 0 + (5426730621/10000000000 : ℝ)*x 1 + (-487376347/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5302182117/10000000000 : ℝ)^4299 ≤ (21740493273597/50000000000000 : ℝ)^3275 := by
    have hnat : (5302182117 : ℕ)^4299*50000000000000^3275 ≤ 21740493273597^3275*10000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5302182117 10000000000 21740493273597 50000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5426730621/10000000000 : ℝ)^4299 ≤ (11206651991249/25000000000000 : ℝ)^3275 := by
    have hnat : (5426730621 : ℕ)^4299*25000000000000^3275 ≤ 11206651991249^3275*10000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5426730621 10000000000 11206651991249 25000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (487376347/2500000000 : ℝ)^4299 ≤ (2338481095513/20000000000000 : ℝ)^3275 := by
    have hnat : (487376347 : ℕ)^4299*20000000000000^3275 ≤ 2338481095513^3275*2500000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      487376347 2500000000 2338481095513 20000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4299/1024 : ℝ)) 4299 3275 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5302182117/10000000000 : ℝ), (5426730621/10000000000 : ℝ), (-487376347/2500000000 : ℝ)] ![(21740493273597/50000000000000 : ℝ), (11206651991249/25000000000000 : ℝ), (2338481095513/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5302182117/10000000000 : ℝ)|^4299 ≤ (21740493273597/50000000000000 : ℝ)^3275
        have hw : |(5302182117/10000000000 : ℝ)|=(5302182117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5426730621/10000000000 : ℝ)|^4299 ≤ (11206651991249/25000000000000 : ℝ)^3275
        have hw : |(5426730621/10000000000 : ℝ)|=(5426730621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-487376347/2500000000 : ℝ)|^4299 ≤ (2338481095513/20000000000000 : ℝ)^3275
        have hw : |(-487376347/2500000000 : ℝ)|=(487376347/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1339_s3_7 (p : ℝ) (hpa : (2149/512 : ℝ) ≤ p) (hpb : p ≤ (4299/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2163180927/5000000000 : ℝ)*x 0 + (4534794881/10000000000 : ℝ)*x 1 + (4126998369/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2163180927/5000000000 : ℝ)^4299 ≤ (33292678005609/100000000000000 : ℝ)^3275 := by
    have hnat : (2163180927 : ℕ)^4299*100000000000000^3275 ≤ 33292678005609^3275*5000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2163180927 5000000000 33292678005609 100000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4534794881/10000000000 : ℝ)^4299 ≤ (8853458035493/25000000000000 : ℝ)^3275 := by
    have hnat : (4534794881 : ℕ)^4299*25000000000000^3275 ≤ 8853458035493^3275*10000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4534794881 10000000000 8853458035493 25000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4126998369/10000000000 : ℝ)^4299 ≤ (31293489832267/100000000000000 : ℝ)^3275 := by
    have hnat : (4126998369 : ℕ)^4299*100000000000000^3275 ≤ 31293489832267^3275*10000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4126998369 10000000000 31293489832267 100000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4299/1024 : ℝ)) 4299 3275 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2163180927/5000000000 : ℝ), (4534794881/10000000000 : ℝ), (4126998369/10000000000 : ℝ)] ![(33292678005609/100000000000000 : ℝ), (8853458035493/25000000000000 : ℝ), (31293489832267/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2163180927/5000000000 : ℝ)|^4299 ≤ (33292678005609/100000000000000 : ℝ)^3275
        have hw : |(2163180927/5000000000 : ℝ)|=(2163180927/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4534794881/10000000000 : ℝ)|^4299 ≤ (8853458035493/25000000000000 : ℝ)^3275
        have hw : |(4534794881/10000000000 : ℝ)|=(4534794881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4126998369/10000000000 : ℝ)|^4299 ≤ (31293489832267/100000000000000 : ℝ)^3275
        have hw : |(4126998369/10000000000 : ℝ)|=(4126998369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1339_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2149/512 : ℝ) ≤ p) (hpb : p ≤ (4299/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77305211/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4029/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1229/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (10853/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3753/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4029/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1229/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4029/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1229/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4029/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1229/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4029/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1229/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4029/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1229/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4029/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1229/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1229/12500 : ℝ) ^ (2149/512 : ℝ) ≤ (369598641045541/6250000000000000000 : ℝ) := by
    have hpowers : (1229/12500 : ℝ)^2149 ≤ (369598641045541/6250000000000000000 : ℝ)^512 := by
      have hnat : (1229 : ℕ)^2149*6250000000000000000^512 ≤ 369598641045541^512*12500^2149 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1229 12500 369598641045541 6250000000000000000 2149 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1229/12500 : ℝ)) (X := (369598641045541/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 2149 512 (by norm_num) hpowers
    exact h
  have hpowhi : (4029/25000 : ℝ) ^ (2149/512 : ℝ) ≤ (47059590369978617/100000000000000000000 : ℝ) := by
    have hpowers : (4029/25000 : ℝ)^2149 ≤ (47059590369978617/100000000000000000000 : ℝ)^512 := by
      have hnat : (4029 : ℕ)^2149*100000000000000000000^512 ≤ 47059590369978617^512*25000^2149 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4029 25000 47059590369978617 100000000000000000000 2149 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4029/25000 : ℝ)) (X := (47059590369978617/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2149 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (3125369598641045541/3125000000000000000 : ℝ) ≤ (400011270788969/400000000000000 : ℝ) ^ (2149/512 : ℝ) := by
    have hpowers : (3125369598641045541/3125000000000000000 : ℝ)^512 ≤ (400011270788969/400000000000000 : ℝ)^2149 := by
      have hnat : (3125369598641045541 : ℕ)^512*400000000000000^2149 ≤ 400011270788969^2149*3125000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3125369598641045541 3125000000000000000 400011270788969 400000000000000 512 2149 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400011270788969/400000000000000 : ℝ)) (X := (3125369598641045541/3125000000000000000 : ℝ)) (by norm_num) 2149 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100052973168626707273/100000000000000000000 : ℝ) ≤ (10001261833029839/10000000000000000 : ℝ) ^ (2149/512 : ℝ) := by
    have hpowers : (100052973168626707273/100000000000000000000 : ℝ)^512 ≤ (10001261833029839/10000000000000000 : ℝ)^2149 := by
      have hnat : (100052973168626707273 : ℕ)^512*10000000000000000^2149 ≤ 10001261833029839^2149*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100052973168626707273 100000000000000000000 10001261833029839 10000000000000000 512 2149 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001261833029839/10000000000000000 : ℝ)) (X := (100052973168626707273/100000000000000000000 : ℝ)) (by norm_num) 2149 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50047059590369978617/50000000000000000000 : ℝ) ≤ (10002241896335453/10000000000000000 : ℝ) ^ (2149/512 : ℝ) := by
    have hpowers : (50047059590369978617/50000000000000000000 : ℝ)^512 ≤ (10002241896335453/10000000000000000 : ℝ)^2149 := by
      have hnat : (50047059590369978617 : ℕ)^512*10000000000000000^2149 ≤ 10002241896335453^2149*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50047059590369978617 50000000000000000000 10002241896335453 10000000000000000 512 2149 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002241896335453/10000000000000000 : ℝ)) (X := (50047059590369978617/50000000000000000000 : ℝ)) (by norm_num) 2149 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(369598641045541/6250000000000000000 : ℝ) ≤ ((15705624669026359051/15710000000000000000 : ℝ)+2*(490031652807/314200000000000 : ℝ)*(1229/12500 : ℝ))^(2149/512 : ℝ) := by
    rw [show (15705624669026359051/15710000000000000000 : ℝ)+2*(490031652807/314200000000000 : ℝ)*(1229/12500 : ℝ)=(400011270788969/400000000000000 : ℝ) by norm_num, show 1+2*(369598641045541/6250000000000000000 : ℝ)=(3125369598641045541/3125000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(47059590369978617/100000000000000000000 : ℝ)+(369598641045541/6250000000000000000 : ℝ) ≤ ((15705624669026359051/15710000000000000000 : ℝ)+(490031652807/314200000000000 : ℝ)*((4029/25000 : ℝ)+(1229/12500 : ℝ)))^(2149/512 : ℝ) := by
    rw [show (15705624669026359051/15710000000000000000 : ℝ)+(490031652807/314200000000000 : ℝ)*((4029/25000 : ℝ)+(1229/12500 : ℝ))=(10001261833029839/10000000000000000 : ℝ) by norm_num, show 1+(47059590369978617/100000000000000000000 : ℝ)+(369598641045541/6250000000000000000 : ℝ)=(100052973168626707273/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(47059590369978617/100000000000000000000 : ℝ) ≤ ((15705624669026359051/15710000000000000000 : ℝ)+2*(490031652807/314200000000000 : ℝ)*(4029/25000 : ℝ))^(2149/512 : ℝ) := by
    rw [show (15705624669026359051/15710000000000000000 : ℝ)+2*(490031652807/314200000000000 : ℝ)*(4029/25000 : ℝ)=(10002241896335453/10000000000000000 : ℝ) by norm_num, show 1+2*(47059590369978617/100000000000000000000 : ℝ)=(50047059590369978617/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (15705624669026359051/15710000000000000000 : ℝ)*(X 1 0+X 2 0)+(490031652807/314200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2149/512 : ℝ)) (lo := (1229/12500 : ℝ)) (hi := (4029/25000 : ℝ)) (c := (15705624669026359051/15710000000000000000 : ℝ)) (alpha := (490031652807/314200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (15705624669026359051/15710000000000000000 : ℝ)*(X 0 1+X 2 1)+(490031652807/314200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2149/512 : ℝ)) (lo := (1229/12500 : ℝ)) (hi := (4029/25000 : ℝ)) (c := (15705624669026359051/15710000000000000000 : ℝ)) (alpha := (490031652807/314200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (15705624669026359051/15710000000000000000 : ℝ)*(X 0 2+X 1 2)+(490031652807/314200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2149/512 : ℝ)) (lo := (1229/12500 : ℝ)) (hi := (4029/25000 : ℝ)) (c := (15705624669026359051/15710000000000000000 : ℝ)) (alpha := (490031652807/314200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-204477467/1000000000 : ℝ)*X 0 0+(1356889003/2500000000 : ℝ)*X 0 1+(130774941/250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1339_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5352795099/10000000000 : ℝ)*X 1 0+(-1072619087/5000000000 : ℝ)*X 1 1+(2615498859/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1339_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((669099359/1250000000 : ℝ)*X 2 0+(1046199603/2000000000 : ℝ)*X 2 1+(-2145238083/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1339_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4326321087/10000000000 : ℝ)*X 0 0+(4125271147/10000000000 : ℝ)*X 0 1+(4536511917/10000000000 : ℝ)*X 0 2+(4326321087/10000000000 : ℝ)*X 1 0+(4125271147/10000000000 : ℝ)*X 1 1+(4536511917/10000000000 : ℝ)*X 1 2+(4326321087/10000000000 : ℝ)*X 2 0+(4125271147/10000000000 : ℝ)*X 2 1+(4536511917/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1339_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2044793971/10000000000 : ℝ)*X 0 0+(2615909179/5000000000 : ℝ)*X 0 1+(2713365221/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1339_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5302182381/10000000000 : ℝ)*X 1 0+(-1949505279/10000000000 : ℝ)*X 1 1+(2713365219/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1339_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5302182117/10000000000 : ℝ)*X 2 0+(5426730621/10000000000 : ℝ)*X 2 1+(-487376347/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1339_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2163180927/5000000000 : ℝ)*X 0 0+(4534794881/10000000000 : ℝ)*X 0 1+(4126998369/10000000000 : ℝ)*X 0 2+(2163180927/5000000000 : ℝ)*X 1 0+(4534794881/10000000000 : ℝ)*X 1 1+(4126998369/10000000000 : ℝ)*X 1 2+(2163180927/5000000000 : ℝ)*X 2 0+(4534794881/10000000000 : ℝ)*X 2 1+(4126998369/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1339_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1385286019105440755400323997/196375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1237536463/100000000000000 : ℝ)*(base19) + (477860573/50000000000000 : ℝ)*(base23) + (154445667/100000000000000 : ℝ)*(upper3) + (35361559/100000000000000 : ℝ)*(upper4) + (164273127/100000000000000 : ℝ)*(upper5) + (1879820810539549/50000000000000 : ℝ)*(major0) + (1879820810539549/50000000000000 : ℝ)*(major1) + (1879820810539549/50000000000000 : ℝ)*(major2) + (5087571660487117/100000000000000 : ℝ)*(sp0) + (1271898678033663/25000000000000 : ℝ)*(sp1) + (5087594993949969/100000000000000 : ℝ)*(sp2) + (607919133809619/25000000000000 : ℝ)*(sp3) + (24289183997/100000000000000 : ℝ)*(sp4) + (10522105627/100000000000000 : ℝ)*(sp7) + (1215843528672051/50000000000000 : ℝ)*(f.failure) + (1017519189934223/20000000000000 : ℝ)*(f.sum) + (12674608776993/1963750000000000000000000000 : ℝ)*base66 + (8437746284197742001/785500000000000000000000000000000 : ℝ)*base68 + (3306483024257742001/785500000000000000000000000000000 : ℝ)*base70 + (11705979848827242001/785500000000000000000000000000000 : ℝ)*base72 + (27483635173431/3927500000000000000000000000 : ℝ)*base74 + (1890240772081257999/785500000000000000000000000000000 : ℝ)*base75 + (7019756302737242001/785500000000000000000000000000000 : ℝ)*base78 + (11408505088725242001/785500000000000000000000000000000 : ℝ)*base80 + (37849886202897/7855000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (2357761/2500000000000000000000 : ℝ)*base89 + (2357761/2500000000000000000000 : ℝ)*base91 + (2357761/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1224310420307067047969717919/392750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (133770039/20000000000000 : ℝ)*(base19) + (217885833/50000000000000 : ℝ)*(base23) + (2232823/5000000000000 : ℝ)*(upper3) + (7895997/25000000000000 : ℝ)*(lower4) + (10851323/12500000000000 : ℝ)*(upper5) + (3791359501017177/100000000000000 : ℝ)*(major0) + (3791359501017177/100000000000000 : ℝ)*(major1) + (3791359501017177/100000000000000 : ℝ)*(major2) + (13241248489/100000000000000 : ℝ)*(sp1) + (4672411451/50000000000000 : ℝ)*(sp2) + (2565258565314511/50000000000000 : ℝ)*(sp4) + (2565251610265169/50000000000000 : ℝ)*(sp5) + (5130507350034453/100000000000000 : ℝ)*(sp6) + (1226100883748049/50000000000000 : ℝ)*(sp7) + (1226100883748049/50000000000000 : ℝ)*(f.failure) + (2565258565314511/50000000000000 : ℝ)*(f.sum) + (30156665591539/15710000000000000000000000000 : ℝ)*base65 + (8353662826418369027/1571000000000000000000000000000000 : ℝ)*base67 + (7252795190293630973/1571000000000000000000000000000000 : ℝ)*base70 + (8649143313561369027/1571000000000000000000000000000000 : ℝ)*base71 + (23766126341339/15710000000000000000000000000 : ℝ)*base73 + (13388749098744369027/1571000000000000000000000000000000 : ℝ)*base75 + (18979559599285369027/1571000000000000000000000000000000 : ℝ)*base77 + (6780402209261369027/1571000000000000000000000000000000 : ℝ)*base79 + (55179036431881/15710000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (26216661/2500000000000000000000 : ℝ)*base90 + (26216661/2500000000000000000000 : ℝ)*base92 + (26216661/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1339_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2149/512 : ℝ) ≤ p) (hpb : p ≤ (4299/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77305211/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4029/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1229/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10853/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3753/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1339_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1339_s4_0 (p : ℝ) (hpa : (2149/512 : ℝ) ≤ p) (hpb : p ≤ (4299/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-81850421/400000000 : ℝ)*x 0 + (216618981/400000000 : ℝ)*x 1 + (5242103501/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (81850421/400000000 : ℝ)^4299 ≤ (6229997517587/50000000000000 : ℝ)^3275 := by
    have hnat : (81850421 : ℕ)^4299*50000000000000^3275 ≤ 6229997517587^3275*400000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      81850421 400000000 6229997517587 50000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (216618981/400000000 : ℝ)^4299 ≤ (44704596505217/100000000000000 : ℝ)^3275 := by
    have hnat : (216618981 : ℕ)^4299*100000000000000^3275 ≤ 44704596505217^3275*400000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216618981 400000000 44704596505217 100000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5242103501/10000000000 : ℝ)^4299 ≤ (8567081687981/20000000000000 : ℝ)^3275 := by
    have hnat : (5242103501 : ℕ)^4299*20000000000000^3275 ≤ 8567081687981^3275*10000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242103501 10000000000 8567081687981 20000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4299/1024 : ℝ)) 4299 3275 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-81850421/400000000 : ℝ), (216618981/400000000 : ℝ), (5242103501/10000000000 : ℝ)] ![(6229997517587/50000000000000 : ℝ), (44704596505217/100000000000000 : ℝ), (8567081687981/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-81850421/400000000 : ℝ)|^4299 ≤ (6229997517587/50000000000000 : ℝ)^3275
        have hw : |(-81850421/400000000 : ℝ)|=(81850421/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(216618981/400000000 : ℝ)|^4299 ≤ (44704596505217/100000000000000 : ℝ)^3275
        have hw : |(216618981/400000000 : ℝ)|=(216618981/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5242103501/10000000000 : ℝ)|^4299 ≤ (8567081687981/20000000000000 : ℝ)^3275
        have hw : |(5242103501/10000000000 : ℝ)|=(5242103501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1339_s4_1 (p : ℝ) (hpa : (2149/512 : ℝ) ≤ p) (hpb : p ≤ (4299/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1069943441/2000000000 : ℝ)*x 0 + (-2134646213/10000000000 : ℝ)*x 1 + (5242103327/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069943441/2000000000 : ℝ)^4299 ≤ (10998350500763/25000000000000 : ℝ)^3275 := by
    have hnat : (1069943441 : ℕ)^4299*25000000000000^3275 ≤ 10998350500763^3275*2000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069943441 2000000000 10998350500763 25000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2134646213/10000000000 : ℝ)^4299 ≤ (3292797852261/25000000000000 : ℝ)^3275 := by
    have hnat : (2134646213 : ℕ)^4299*25000000000000^3275 ≤ 3292797852261^3275*10000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2134646213 10000000000 3292797852261 25000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5242103327/10000000000 : ℝ)^4299 ≤ (21417703286757/50000000000000 : ℝ)^3275 := by
    have hnat : (5242103327 : ℕ)^4299*50000000000000^3275 ≤ 21417703286757^3275*10000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242103327 10000000000 21417703286757 50000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4299/1024 : ℝ)) 4299 3275 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069943441/2000000000 : ℝ), (-2134646213/10000000000 : ℝ), (5242103327/10000000000 : ℝ)] ![(10998350500763/25000000000000 : ℝ), (3292797852261/25000000000000 : ℝ), (21417703286757/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069943441/2000000000 : ℝ)|^4299 ≤ (10998350500763/25000000000000 : ℝ)^3275
        have hw : |(1069943441/2000000000 : ℝ)|=(1069943441/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2134646213/10000000000 : ℝ)|^4299 ≤ (3292797852261/25000000000000 : ℝ)^3275
        have hw : |(-2134646213/10000000000 : ℝ)|=(2134646213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5242103327/10000000000 : ℝ)|^4299 ≤ (21417703286757/50000000000000 : ℝ)^3275
        have hw : |(5242103327/10000000000 : ℝ)|=(5242103327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1339_s4_2 (p : ℝ) (hpa : (2149/512 : ℝ) ≤ p) (hpb : p ≤ (4299/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349717569/10000000000 : ℝ)*x 0 + (5242102971/10000000000 : ℝ)*x 1 + (-2134646199/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349717569/10000000000 : ℝ)^4299 ≤ (43993405932343/100000000000000 : ℝ)^3275 := by
    have hnat : (5349717569 : ℕ)^4299*100000000000000^3275 ≤ 43993405932343^3275*10000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349717569 10000000000 43993405932343 100000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5242102971/10000000000 : ℝ)^4299 ≤ (1070885068873/2500000000000 : ℝ)^3275 := by
    have hnat : (5242102971 : ℕ)^4299*2500000000000^3275 ≤ 1070885068873^3275*10000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242102971 10000000000 1070885068873 2500000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2134646199/10000000000 : ℝ)^4299 ≤ (3292797823913/25000000000000 : ℝ)^3275 := by
    have hnat : (2134646199 : ℕ)^4299*25000000000000^3275 ≤ 3292797823913^3275*10000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2134646199 10000000000 3292797823913 25000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4299/1024 : ℝ)) 4299 3275 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349717569/10000000000 : ℝ), (5242102971/10000000000 : ℝ), (-2134646199/10000000000 : ℝ)] ![(43993405932343/100000000000000 : ℝ), (1070885068873/2500000000000 : ℝ), (3292797823913/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349717569/10000000000 : ℝ)|^4299 ≤ (43993405932343/100000000000000 : ℝ)^3275
        have hw : |(5349717569/10000000000 : ℝ)|=(5349717569/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5242102971/10000000000 : ℝ)|^4299 ≤ (1070885068873/2500000000000 : ℝ)^3275
        have hw : |(5242102971/10000000000 : ℝ)|=(5242102971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2134646199/10000000000 : ℝ)|^4299 ≤ (3292797823913/25000000000000 : ℝ)^3275
        have hw : |(-2134646199/10000000000 : ℝ)|=(2134646199/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1339_s4_3 (p : ℝ) (hpa : (2149/512 : ℝ) ≤ p) (hpb : p ≤ (4299/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (540902933/1250000000 : ℝ)*x 0 + (32417303/78125000 : ℝ)*x 1 + (70502251/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (540902933/1250000000 : ℝ)^4299 ≤ (8325345438271/25000000000000 : ℝ)^3275 := by
    have hnat : (540902933 : ℕ)^4299*25000000000000^3275 ≤ 8325345438271^3275*1250000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540902933 1250000000 8325345438271 25000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (32417303/78125000 : ℝ)^4299 ≤ (31516800860993/100000000000000 : ℝ)^3275 := by
    have hnat : (32417303 : ℕ)^4299*100000000000000^3275 ≤ 31516800860993^3275*78125000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      32417303 78125000 31516800860993 100000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (70502251/156250000 : ℝ)^4299 ≤ (35181817370911/100000000000000 : ℝ)^3275 := by
    have hnat : (70502251 : ℕ)^4299*100000000000000^3275 ≤ 35181817370911^3275*156250000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      70502251 156250000 35181817370911 100000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4299/1024 : ℝ)) 4299 3275 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(540902933/1250000000 : ℝ), (32417303/78125000 : ℝ), (70502251/156250000 : ℝ)] ![(8325345438271/25000000000000 : ℝ), (31516800860993/100000000000000 : ℝ), (35181817370911/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(540902933/1250000000 : ℝ)|^4299 ≤ (8325345438271/25000000000000 : ℝ)^3275
        have hw : |(540902933/1250000000 : ℝ)|=(540902933/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(32417303/78125000 : ℝ)|^4299 ≤ (31516800860993/100000000000000 : ℝ)^3275
        have hw : |(32417303/78125000 : ℝ)|=(32417303/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(70502251/156250000 : ℝ)|^4299 ≤ (35181817370911/100000000000000 : ℝ)^3275
        have hw : |(70502251/156250000 : ℝ)|=(70502251/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1339_s4_4 (p : ℝ) (hpa : (2149/512 : ℝ) ≤ p) (hpb : p ≤ (4299/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1023136911/5000000000 : ℝ)*x 0 + (5242742507/10000000000 : ℝ)*x 1 + (1353708039/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1023136911/5000000000 : ℝ)^4299 ≤ (12460101319003/100000000000000 : ℝ)^3275 := by
    have hnat : (1023136911 : ℕ)^4299*100000000000000^3275 ≤ 12460101319003^3275*5000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1023136911 5000000000 12460101319003 100000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5242742507/10000000000 : ℝ)^4299 ≤ (42842262796169/100000000000000 : ℝ)^3275 := by
    have hnat : (5242742507 : ℕ)^4299*100000000000000^3275 ≤ 42842262796169^3275*10000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242742507 10000000000 42842262796169 100000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1353708039/2500000000 : ℝ)^4299 ≤ (22348817939417/50000000000000 : ℝ)^3275 := by
    have hnat : (1353708039 : ℕ)^4299*50000000000000^3275 ≤ 22348817939417^3275*2500000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1353708039 2500000000 22348817939417 50000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4299/1024 : ℝ)) 4299 3275 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1023136911/5000000000 : ℝ), (5242742507/10000000000 : ℝ), (1353708039/2500000000 : ℝ)] ![(12460101319003/100000000000000 : ℝ), (42842262796169/100000000000000 : ℝ), (22348817939417/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1023136911/5000000000 : ℝ)|^4299 ≤ (12460101319003/100000000000000 : ℝ)^3275
        have hw : |(-1023136911/5000000000 : ℝ)|=(1023136911/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5242742507/10000000000 : ℝ)|^4299 ≤ (42842262796169/100000000000000 : ℝ)^3275
        have hw : |(5242742507/10000000000 : ℝ)|=(5242742507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1353708039/2500000000 : ℝ)|^4299 ≤ (22348817939417/50000000000000 : ℝ)^3275
        have hw : |(1353708039/2500000000 : ℝ)|=(1353708039/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1339_s4_5 (p : ℝ) (hpa : (2149/512 : ℝ) ≤ p) (hpb : p ≤ (4299/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305075913/10000000000 : ℝ)*x 0 + (-980958699/5000000000 : ℝ)*x 1 + (5414832417/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305075913/10000000000 : ℝ)^4299 ≤ (10878034993967/25000000000000 : ℝ)^3275 := by
    have hnat : (5305075913 : ℕ)^4299*25000000000000^3275 ≤ 10878034993967^3275*10000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305075913 10000000000 10878034993967 25000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (980958699/5000000000 : ℝ)^4299 ≤ (11790221301569/100000000000000 : ℝ)^3275 := by
    have hnat : (980958699 : ℕ)^4299*100000000000000^3275 ≤ 11790221301569^3275*5000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      980958699 5000000000 11790221301569 100000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5414832417/10000000000 : ℝ)^4299 ≤ (174600151199/390625000000 : ℝ)^3275 := by
    have hnat : (5414832417 : ℕ)^4299*390625000000^3275 ≤ 174600151199^3275*10000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5414832417 10000000000 174600151199 390625000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4299/1024 : ℝ)) 4299 3275 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305075913/10000000000 : ℝ), (-980958699/5000000000 : ℝ), (5414832417/10000000000 : ℝ)] ![(10878034993967/25000000000000 : ℝ), (11790221301569/100000000000000 : ℝ), (174600151199/390625000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305075913/10000000000 : ℝ)|^4299 ≤ (10878034993967/25000000000000 : ℝ)^3275
        have hw : |(5305075913/10000000000 : ℝ)|=(5305075913/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-980958699/5000000000 : ℝ)|^4299 ≤ (11790221301569/100000000000000 : ℝ)^3275
        have hw : |(-980958699/5000000000 : ℝ)|=(980958699/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5414832417/10000000000 : ℝ)|^4299 ≤ (174600151199/390625000000 : ℝ)^3275
        have hw : |(5414832417/10000000000 : ℝ)|=(5414832417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1339_s4_6 (p : ℝ) (hpa : (2149/512 : ℝ) ≤ p) (hpb : p ≤ (4299/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1061015233/2000000000 : ℝ)*x 0 + (16921351/31250000 : ℝ)*x 1 + (-1961917187/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1061015233/2000000000 : ℝ)^4299 ≤ (43512142689029/100000000000000 : ℝ)^3275 := by
    have hnat : (1061015233 : ℕ)^4299*100000000000000^3275 ≤ 43512142689029^3275*2000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061015233 2000000000 43512142689029 100000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (16921351/31250000 : ℝ)^4299 ≤ (11174409413971/25000000000000 : ℝ)^3275 := by
    have hnat : (16921351 : ℕ)^4299*25000000000000^3275 ≤ 11174409413971^3275*31250000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16921351 31250000 11174409413971 25000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1961917187/10000000000 : ℝ)^4299 ≤ (2358043927417/20000000000000 : ℝ)^3275 := by
    have hnat : (1961917187 : ℕ)^4299*20000000000000^3275 ≤ 2358043927417^3275*10000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1961917187 10000000000 2358043927417 20000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4299/1024 : ℝ)) 4299 3275 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1061015233/2000000000 : ℝ), (16921351/31250000 : ℝ), (-1961917187/10000000000 : ℝ)] ![(43512142689029/100000000000000 : ℝ), (11174409413971/25000000000000 : ℝ), (2358043927417/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1061015233/2000000000 : ℝ)|^4299 ≤ (43512142689029/100000000000000 : ℝ)^3275
        have hw : |(1061015233/2000000000 : ℝ)|=(1061015233/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(16921351/31250000 : ℝ)|^4299 ≤ (11174409413971/25000000000000 : ℝ)^3275
        have hw : |(16921351/31250000 : ℝ)|=(16921351/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1961917187/10000000000 : ℝ)|^4299 ≤ (2358043927417/20000000000000 : ℝ)^3275
        have hw : |(-1961917187/10000000000 : ℝ)|=(1961917187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1339_s4_7 (p : ℝ) (hpa : (2149/512 : ℝ) ≤ p) (hpb : p ≤ (4299/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2163625519/5000000000 : ℝ)*x 0 + (1127701759/2500000000 : ℝ)*x 1 + (103768981/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2163625519/5000000000 : ℝ)^4299 ≤ (8325415076751/25000000000000 : ℝ)^3275 := by
    have hnat : (2163625519 : ℕ)^4299*25000000000000^3275 ≤ 8325415076751^3275*5000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2163625519 5000000000 8325415076751 25000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1127701759/2500000000 : ℝ)^4299 ≤ (17584066704841/50000000000000 : ℝ)^3275 := by
    have hnat : (1127701759 : ℕ)^4299*50000000000000^3275 ≤ 17584066704841^3275*2500000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1127701759 2500000000 17584066704841 50000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (103768981/250000000 : ℝ)^4299 ≤ (15765103134071/50000000000000 : ℝ)^3275 := by
    have hnat : (103768981 : ℕ)^4299*50000000000000^3275 ≤ 15765103134071^3275*250000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      103768981 250000000 15765103134071 50000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4299/1024 : ℝ)) 4299 3275 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2163625519/5000000000 : ℝ), (1127701759/2500000000 : ℝ), (103768981/250000000 : ℝ)] ![(8325415076751/25000000000000 : ℝ), (17584066704841/50000000000000 : ℝ), (15765103134071/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2163625519/5000000000 : ℝ)|^4299 ≤ (8325415076751/25000000000000 : ℝ)^3275
        have hw : |(2163625519/5000000000 : ℝ)|=(2163625519/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1127701759/2500000000 : ℝ)|^4299 ≤ (17584066704841/50000000000000 : ℝ)^3275
        have hw : |(1127701759/2500000000 : ℝ)|=(1127701759/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(103768981/250000000 : ℝ)|^4299 ≤ (15765103134071/50000000000000 : ℝ)^3275
        have hw : |(103768981/250000000 : ℝ)|=(103768981/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1339_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2149/512 : ℝ) ≤ p) (hpb : p ≤ (4299/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77305211/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3753/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10853/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1109/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (369/2500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3753/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10853/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3753/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10853/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3753/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10853/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3753/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10853/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3753/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10853/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3753/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10853/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10853/100000 : ℝ) ^ (2149/512 : ℝ) ≤ (8952541464234691/100000000000000000000 : ℝ) := by
    have hpowers : (10853/100000 : ℝ)^2149 ≤ (8952541464234691/100000000000000000000 : ℝ)^512 := by
      have hnat : (10853 : ℕ)^2149*100000000000000000000^512 ≤ 8952541464234691^512*100000^2149 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10853 100000 8952541464234691 100000000000000000000 2149 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10853/100000 : ℝ)) (X := (8952541464234691/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2149 512 (by norm_num) hpowers
    exact h
  have hpowhi : (3753/25000 : ℝ) ^ (2149/512 : ℝ) ≤ (6987532737099637/20000000000000000000 : ℝ) := by
    have hpowers : (3753/25000 : ℝ)^2149 ≤ (6987532737099637/20000000000000000000 : ℝ)^512 := by
      have hnat : (3753 : ℕ)^2149*20000000000000000000^512 ≤ 6987532737099637^512*25000^2149 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3753 25000 6987532737099637 20000000000000000000 2149 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3753/25000 : ℝ)) (X := (6987532737099637/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2149 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50008952541464234691/50000000000000000000 : ℝ) ≤ (10000426560137057/10000000000000000 : ℝ) ^ (2149/512 : ℝ) := by
    have hpowers : (50008952541464234691/50000000000000000000 : ℝ)^512 ≤ (10000426560137057/10000000000000000 : ℝ)^2149 := by
      have hnat : (50008952541464234691 : ℕ)^512*10000000000000000^2149 ≤ 10000426560137057^2149*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50008952541464234691 50000000000000000000 10000426560137057 10000000000000000 512 2149 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000426560137057/10000000000000000 : ℝ)) (X := (50008952541464234691/50000000000000000000 : ℝ)) (by norm_num) 2149 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (25010972551287433219/25000000000000000000 : ℝ) ≤ (10001045510910633/10000000000000000 : ℝ) ^ (2149/512 : ℝ) := by
    have hpowers : (25010972551287433219/25000000000000000000 : ℝ)^512 ≤ (10001045510910633/10000000000000000 : ℝ)^2149 := by
      have hnat : (25010972551287433219 : ℕ)^512*10000000000000000^2149 ≤ 10001045510910633^2149*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25010972551287433219 25000000000000000000 10001045510910633 10000000000000000 512 2149 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001045510910633/10000000000000000 : ℝ)) (X := (25010972551287433219/25000000000000000000 : ℝ)) (by norm_num) 2149 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (10006987532737099637/10000000000000000000 : ℝ) ≤ (10001664461684209/10000000000000000 : ℝ) ^ (2149/512 : ℝ) := by
    have hpowers : (10006987532737099637/10000000000000000000 : ℝ)^512 ≤ (10001664461684209/10000000000000000 : ℝ)^2149 := by
      have hnat : (10006987532737099637 : ℕ)^512*10000000000000000^2149 ≤ 10001664461684209^2149*10000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10006987532737099637 10000000000000000000 10001664461684209 10000000000000000 512 2149 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001664461684209/10000000000000000 : ℝ)) (X := (10006987532737099637/10000000000000000000 : ℝ)) (by norm_num) 2149 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(8952541464234691/100000000000000000000 : ℝ) ≤ ((41578339118118779407/41590000000000000000 : ℝ)+2*(77368846697/51987500000000 : ℝ)*(10853/100000 : ℝ))^(2149/512 : ℝ) := by
    rw [show (41578339118118779407/41590000000000000000 : ℝ)+2*(77368846697/51987500000000 : ℝ)*(10853/100000 : ℝ)=(10000426560137057/10000000000000000 : ℝ) by norm_num, show 1+2*(8952541464234691/100000000000000000000 : ℝ)=(50008952541464234691/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(6987532737099637/20000000000000000000 : ℝ)+(8952541464234691/100000000000000000000 : ℝ) ≤ ((41578339118118779407/41590000000000000000 : ℝ)+(77368846697/51987500000000 : ℝ)*((3753/25000 : ℝ)+(10853/100000 : ℝ)))^(2149/512 : ℝ) := by
    rw [show (41578339118118779407/41590000000000000000 : ℝ)+(77368846697/51987500000000 : ℝ)*((3753/25000 : ℝ)+(10853/100000 : ℝ))=(10001045510910633/10000000000000000 : ℝ) by norm_num, show 1+(6987532737099637/20000000000000000000 : ℝ)+(8952541464234691/100000000000000000000 : ℝ)=(25010972551287433219/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(6987532737099637/20000000000000000000 : ℝ) ≤ ((41578339118118779407/41590000000000000000 : ℝ)+2*(77368846697/51987500000000 : ℝ)*(3753/25000 : ℝ))^(2149/512 : ℝ) := by
    rw [show (41578339118118779407/41590000000000000000 : ℝ)+2*(77368846697/51987500000000 : ℝ)*(3753/25000 : ℝ)=(10001664461684209/10000000000000000 : ℝ) by norm_num, show 1+2*(6987532737099637/20000000000000000000 : ℝ)=(10006987532737099637/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (41578339118118779407/41590000000000000000 : ℝ)*(X 1 0+X 2 0)+(77368846697/51987500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2149/512 : ℝ)) (lo := (10853/100000 : ℝ)) (hi := (3753/25000 : ℝ)) (c := (41578339118118779407/41590000000000000000 : ℝ)) (alpha := (77368846697/51987500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (41578339118118779407/41590000000000000000 : ℝ)*(X 0 1+X 2 1)+(77368846697/51987500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2149/512 : ℝ)) (lo := (10853/100000 : ℝ)) (hi := (3753/25000 : ℝ)) (c := (41578339118118779407/41590000000000000000 : ℝ)) (alpha := (77368846697/51987500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (41578339118118779407/41590000000000000000 : ℝ)*(X 0 2+X 1 2)+(77368846697/51987500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2149/512 : ℝ)) (lo := (10853/100000 : ℝ)) (hi := (3753/25000 : ℝ)) (c := (41578339118118779407/41590000000000000000 : ℝ)) (alpha := (77368846697/51987500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-81850421/400000000 : ℝ)*X 0 0+(216618981/400000000 : ℝ)*X 0 1+(5242103501/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1339_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1069943441/2000000000 : ℝ)*X 1 0+(-2134646213/10000000000 : ℝ)*X 1 1+(5242103327/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1339_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5349717569/10000000000 : ℝ)*X 2 0+(5242102971/10000000000 : ℝ)*X 2 1+(-2134646199/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1339_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((540902933/1250000000 : ℝ)*X 0 0+(32417303/78125000 : ℝ)*X 0 1+(70502251/156250000 : ℝ)*X 0 2+(540902933/1250000000 : ℝ)*X 1 0+(32417303/78125000 : ℝ)*X 1 1+(70502251/156250000 : ℝ)*X 1 2+(540902933/1250000000 : ℝ)*X 2 0+(32417303/78125000 : ℝ)*X 2 1+(70502251/156250000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1339_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1023136911/5000000000 : ℝ)*X 0 0+(5242742507/10000000000 : ℝ)*X 0 1+(1353708039/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1339_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305075913/10000000000 : ℝ)*X 1 0+(-980958699/5000000000 : ℝ)*X 1 1+(5414832417/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1339_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1061015233/2000000000 : ℝ)*X 2 0+(16921351/31250000 : ℝ)*X 2 1+(-1961917187/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1339_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2163625519/5000000000 : ℝ)*X 0 0+(1127701759/2500000000 : ℝ)*X 0 1+(103768981/250000000 : ℝ)*X 0 2+(2163625519/5000000000 : ℝ)*X 1 0+(1127701759/2500000000 : ℝ)*X 1 1+(103768981/250000000 : ℝ)*X 1 2+(2163625519/5000000000 : ℝ)*X 2 0+(1127701759/2500000000 : ℝ)*X 2 1+(103768981/250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1339_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3840724132525113723352351881/519875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (87404269/5000000000000 : ℝ)*(base19) + (429599383/25000000000000 : ℝ)*(base23) + (283288349/100000000000000 : ℝ)*(lower2) + (5683713/2500000000000 : ℝ)*(upper3) + (14362443/25000000000000 : ℝ)*(lower4) + (1065618473382539/25000000000000 : ℝ)*(major0) + (1065618473382539/25000000000000 : ℝ)*(major1) + (1065618473382539/25000000000000 : ℝ)*(major2) + (144200149076553/2500000000000 : ℝ)*(sp0) + (721004174273781/12500000000000 : ℝ)*(sp1) + (360502088992381/6250000000000 : ℝ)*(sp2) + (1378445725628867/50000000000000 : ℝ)*(sp3) + (29179213507/100000000000000 : ℝ)*(sp4) + (523681687/2500000000000 : ℝ)*(sp7) + (551382479705043/20000000000000 : ℝ)*(f.failure) + (5768035142275627/100000000000000 : ℝ)*(f.sum) + (31381606604283/10397500000000000000000000000 : ℝ)*base65 + (1760439878759224373/1039750000000000000000000000000000 : ℝ)*base67 + (2016888390539974373/1039750000000000000000000000000000 : ℝ)*base69 + (6922686915113025627/1039750000000000000000000000000000 : ℝ)*base72 + (16295944172227/2599375000000000000000000000 : ℝ)*base73 + (887572366650974373/1039750000000000000000000000000000 : ℝ)*base75 + (6056874392472974373/1039750000000000000000000000000000 : ℝ)*base77 + (12331799442879025627/1039750000000000000000000000000000 : ℝ)*base80 + (7913052062851/1299687500000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (6879073/1000000000000000000000 : ℝ)*base89 + (6879073/1000000000000000000000 : ℝ)*base91 + (6879073/1000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7932473858544828498473076033/1039750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (5735767/1562500000000 : ℝ)*(base19) + (33561873/2500000000000 : ℝ)*(base23) + (4670693/5000000000000 : ℝ)*(upper3) + (5523479/2000000000000 : ℝ)*(lower4) + (23921903/100000000000000 : ℝ)*(upper5) + (4294164531297973/100000000000000 : ℝ)*(major0) + (4294164531297973/100000000000000 : ℝ)*(major1) + (4294164531297973/100000000000000 : ℝ)*(major2) + (6558467719/50000000000000 : ℝ)*(sp1) + (6872373417/20000000000000 : ℝ)*(sp2) + (1452729829872819/25000000000000 : ℝ)*(sp4) + (23243623341867/400000000000 : ℝ)*(sp5) + (5810883615149271/100000000000000 : ℝ)*(sp6) + (111096379551903/4000000000000 : ℝ)*(sp7) + (111096379551903/4000000000000 : ℝ)*(f.failure) + (1452729829872819/25000000000000 : ℝ)*(f.sum) + (49452100650531/10397500000000000000000000000 : ℝ)*base66 + (23663878086169957989/4159000000000000000000000000000000 : ℝ)*base68 + (35142333062585957989/4159000000000000000000000000000000 : ℝ)*base70 + (55739041649691957989/4159000000000000000000000000000000 : ℝ)*base72 + (54860101420589/10397500000000000000000000000 : ℝ)*base73 + (64102971923865957989/4159000000000000000000000000000000 : ℝ)*base76 + (25321523637551957989/4159000000000000000000000000000000 : ℝ)*base78 + (4118327909473042011/4159000000000000000000000000000000 : ℝ)*base79 + (570120157057/1299687500000000000000000000 : ℝ)*base82 + (866533/200000000000000000000 : ℝ)*base89 + (866533/200000000000000000000 : ℝ)*base91 + (866533/200000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1339_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2149/512 : ℝ) ≤ p) (hpb : p ≤ (4299/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77305211/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3753/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10853/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1109/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (369/2500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1339_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1339_s5_0 (p : ℝ) (hpa : (2149/512 : ℝ) ≤ p) (hpb : p ≤ (4299/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-409303447/2000000000 : ℝ)*x 0 + (338328759/625000000 : ℝ)*x 1 + (32775931/62500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (409303447/2000000000 : ℝ)^4299 ≤ (124620469739/1000000000000 : ℝ)^3275 := by
    have hnat : (409303447 : ℕ)^4299*1000000000000^3275 ≤ 124620469739^3275*2000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      409303447 2000000000 124620469739 1000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (338328759/625000000 : ℝ)^4299 ≤ (44680602851683/100000000000000 : ℝ)^3275 := by
    have hnat : (338328759 : ℕ)^4299*100000000000000^3275 ≤ 44680602851683^3275*625000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      338328759 625000000 44680602851683 100000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (32775931/62500000 : ℝ)^4299 ≤ (21428675081501/50000000000000 : ℝ)^3275 := by
    have hnat : (32775931 : ℕ)^4299*50000000000000^3275 ≤ 21428675081501^3275*62500000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      32775931 62500000 21428675081501 50000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4299/1024 : ℝ)) 4299 3275 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-409303447/2000000000 : ℝ), (338328759/625000000 : ℝ), (32775931/62500000 : ℝ)] ![(124620469739/1000000000000 : ℝ), (44680602851683/100000000000000 : ℝ), (21428675081501/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-409303447/2000000000 : ℝ)|^4299 ≤ (124620469739/1000000000000 : ℝ)^3275
        have hw : |(-409303447/2000000000 : ℝ)|=(409303447/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(338328759/625000000 : ℝ)|^4299 ≤ (44680602851683/100000000000000 : ℝ)^3275
        have hw : |(338328759/625000000 : ℝ)|=(338328759/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(32775931/62500000 : ℝ)|^4299 ≤ (21428675081501/50000000000000 : ℝ)^3275
        have hw : |(32775931/62500000 : ℝ)|=(32775931/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1339_s5_1 (p : ℝ) (hpa : (2149/512 : ℝ) ≤ p) (hpb : p ≤ (4299/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (668643967/1250000000 : ℝ)*x 0 + (-2132690293/10000000000 : ℝ)*x 1 + (5244148961/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668643967/1250000000 : ℝ)^4299 ≤ (43987298003583/100000000000000 : ℝ)^3275 := by
    have hnat : (668643967 : ℕ)^4299*100000000000000^3275 ≤ 43987298003583^3275*1250000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668643967 1250000000 43987298003583 100000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2132690293/10000000000 : ℝ)^4299 ≤ (6577675905553/50000000000000 : ℝ)^3275 := by
    have hnat : (2132690293 : ℕ)^4299*50000000000000^3275 ≤ 6577675905553^3275*10000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2132690293 10000000000 6577675905553 50000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5244148961/10000000000 : ℝ)^4299 ≤ (4285735017373/10000000000000 : ℝ)^3275 := by
    have hnat : (5244148961 : ℕ)^4299*10000000000000^3275 ≤ 4285735017373^3275*10000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244148961 10000000000 4285735017373 10000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4299/1024 : ℝ)) 4299 3275 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668643967/1250000000 : ℝ), (-2132690293/10000000000 : ℝ), (5244148961/10000000000 : ℝ)] ![(43987298003583/100000000000000 : ℝ), (6577675905553/50000000000000 : ℝ), (4285735017373/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668643967/1250000000 : ℝ)|^4299 ≤ (43987298003583/100000000000000 : ℝ)^3275
        have hw : |(668643967/1250000000 : ℝ)|=(668643967/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2132690293/10000000000 : ℝ)|^4299 ≤ (6577675905553/50000000000000 : ℝ)^3275
        have hw : |(-2132690293/10000000000 : ℝ)|=(2132690293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5244148961/10000000000 : ℝ)|^4299 ≤ (4285735017373/10000000000000 : ℝ)^3275
        have hw : |(5244148961/10000000000 : ℝ)|=(5244148961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1339_s5_2 (p : ℝ) (hpa : (2149/512 : ℝ) ≤ p) (hpb : p ≤ (4299/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349151751/10000000000 : ℝ)*x 0 + (32775931/62500000 : ℝ)*x 1 + (-2132690273/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349151751/10000000000 : ℝ)^4299 ≤ (43987298165499/100000000000000 : ℝ)^3275 := by
    have hnat : (5349151751 : ℕ)^4299*100000000000000^3275 ≤ 43987298165499^3275*10000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349151751 10000000000 43987298165499 100000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (32775931/62500000 : ℝ)^4299 ≤ (21428675081501/50000000000000 : ℝ)^3275 := by
    have hnat : (32775931 : ℕ)^4299*50000000000000^3275 ≤ 21428675081501^3275*62500000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      32775931 62500000 21428675081501 50000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2132690273/10000000000 : ℝ)^4299 ≤ (13155351649163/100000000000000 : ℝ)^3275 := by
    have hnat : (2132690273 : ℕ)^4299*100000000000000^3275 ≤ 13155351649163^3275*10000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2132690273 10000000000 13155351649163 100000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4299/1024 : ℝ)) 4299 3275 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349151751/10000000000 : ℝ), (32775931/62500000 : ℝ), (-2132690273/10000000000 : ℝ)] ![(43987298165499/100000000000000 : ℝ), (21428675081501/50000000000000 : ℝ), (13155351649163/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349151751/10000000000 : ℝ)|^4299 ≤ (43987298165499/100000000000000 : ℝ)^3275
        have hw : |(5349151751/10000000000 : ℝ)|=(5349151751/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(32775931/62500000 : ℝ)|^4299 ≤ (21428675081501/50000000000000 : ℝ)^3275
        have hw : |(32775931/62500000 : ℝ)|=(32775931/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2132690273/10000000000 : ℝ)|^4299 ≤ (13155351649163/100000000000000 : ℝ)^3275
        have hw : |(-2132690273/10000000000 : ℝ)|=(2132690273/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1339_s5_3 (p : ℝ) (hpa : (2149/512 : ℝ) ≤ p) (hpb : p ≤ (4299/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2163688267/5000000000 : ℝ)*x 0 + (4153852647/10000000000 : ℝ)*x 1 + (880404/1953125 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2163688267/5000000000 : ℝ)^4299 ≤ (33302928080853/100000000000000 : ℝ)^3275 := by
    have hnat : (2163688267 : ℕ)^4299*100000000000000^3275 ≤ 33302928080853^3275*5000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2163688267 5000000000 33302928080853 100000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4153852647/10000000000 : ℝ)^4299 ≤ (15780527704087/50000000000000 : ℝ)^3275 := by
    have hnat : (4153852647 : ℕ)^4299*50000000000000^3275 ≤ 15780527704087^3275*10000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4153852647 10000000000 15780527704087 50000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (880404/1953125 : ℝ)^4299 ≤ (8784004123329/25000000000000 : ℝ)^3275 := by
    have hnat : (880404 : ℕ)^4299*25000000000000^3275 ≤ 8784004123329^3275*1953125^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      880404 1953125 8784004123329 25000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4299/1024 : ℝ)) 4299 3275 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2163688267/5000000000 : ℝ), (4153852647/10000000000 : ℝ), (880404/1953125 : ℝ)] ![(33302928080853/100000000000000 : ℝ), (15780527704087/50000000000000 : ℝ), (8784004123329/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2163688267/5000000000 : ℝ)|^4299 ≤ (33302928080853/100000000000000 : ℝ)^3275
        have hw : |(2163688267/5000000000 : ℝ)|=(2163688267/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4153852647/10000000000 : ℝ)|^4299 ≤ (15780527704087/50000000000000 : ℝ)^3275
        have hw : |(4153852647/10000000000 : ℝ)|=(4153852647/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(880404/1953125 : ℝ)|^4299 ≤ (8784004123329/25000000000000 : ℝ)^3275
        have hw : |(880404/1953125 : ℝ)|=(880404/1953125 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1339_s5_4 (p : ℝ) (hpa : (2149/512 : ℝ) ≤ p) (hpb : p ≤ (4299/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2046529599/10000000000 : ℝ)*x 0 + (1048951399/2000000000 : ℝ)*x 1 + (541264897/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2046529599/10000000000 : ℝ)^4299 ≤ (6231072902033/50000000000000 : ℝ)^3275 := by
    have hnat : (2046529599 : ℕ)^4299*50000000000000^3275 ≤ 6231072902033^3275*10000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2046529599 10000000000 6231072902033 50000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1048951399/2000000000 : ℝ)^4299 ≤ (21431936547777/50000000000000 : ℝ)^3275 := by
    have hnat : (1048951399 : ℕ)^4299*50000000000000^3275 ≤ 21431936547777^3275*2000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048951399 2000000000 21431936547777 50000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (541264897/1000000000 : ℝ)^4299 ≤ (22336990545573/50000000000000 : ℝ)^3275 := by
    have hnat : (541264897 : ℕ)^4299*50000000000000^3275 ≤ 22336990545573^3275*1000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      541264897 1000000000 22336990545573 50000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4299/1024 : ℝ)) 4299 3275 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2046529599/10000000000 : ℝ), (1048951399/2000000000 : ℝ), (541264897/1000000000 : ℝ)] ![(6231072902033/50000000000000 : ℝ), (21431936547777/50000000000000 : ℝ), (22336990545573/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2046529599/10000000000 : ℝ)|^4299 ≤ (6231072902033/50000000000000 : ℝ)^3275
        have hw : |(-2046529599/10000000000 : ℝ)|=(2046529599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1048951399/2000000000 : ℝ)|^4299 ≤ (21431936547777/50000000000000 : ℝ)^3275
        have hw : |(1048951399/2000000000 : ℝ)|=(1048951399/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(541264897/1000000000 : ℝ)|^4299 ≤ (22336990545573/50000000000000 : ℝ)^3275
        have hw : |(541264897/1000000000 : ℝ)|=(541264897/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1339_s5_5 (p : ℝ) (hpa : (2149/512 : ℝ) ≤ p) (hpb : p ≤ (4299/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305607617/10000000000 : ℝ)*x 0 + (-30690473/156250000 : ℝ)*x 1 + (5412648969/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305607617/10000000000 : ℝ)^4299 ≤ (43517864662429/100000000000000 : ℝ)^3275 := by
    have hnat : (5305607617 : ℕ)^4299*100000000000000^3275 ≤ 43517864662429^3275*10000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305607617 10000000000 43517864662429 100000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (30690473/156250000 : ℝ)^4299 ≤ (1476019279543/12500000000000 : ℝ)^3275 := by
    have hnat : (30690473 : ℕ)^4299*12500000000000^3275 ≤ 1476019279543^3275*156250000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      30690473 156250000 1476019279543 12500000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5412648969/10000000000 : ℝ)^4299 ≤ (5584247635039/12500000000000 : ℝ)^3275 := by
    have hnat : (5412648969 : ℕ)^4299*12500000000000^3275 ≤ 5584247635039^3275*10000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5412648969 10000000000 5584247635039 12500000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4299/1024 : ℝ)) 4299 3275 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305607617/10000000000 : ℝ), (-30690473/156250000 : ℝ), (5412648969/10000000000 : ℝ)] ![(43517864662429/100000000000000 : ℝ), (1476019279543/12500000000000 : ℝ), (5584247635039/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305607617/10000000000 : ℝ)|^4299 ≤ (43517864662429/100000000000000 : ℝ)^3275
        have hw : |(5305607617/10000000000 : ℝ)|=(5305607617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-30690473/156250000 : ℝ)|^4299 ≤ (1476019279543/12500000000000 : ℝ)^3275
        have hw : |(-30690473/156250000 : ℝ)|=(30690473/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5412648969/10000000000 : ℝ)|^4299 ≤ (5584247635039/12500000000000 : ℝ)^3275
        have hw : |(5412648969/10000000000 : ℝ)|=(5412648969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1339_s5_6 (p : ℝ) (hpa : (2149/512 : ℝ) ≤ p) (hpb : p ≤ (4299/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2652803809/5000000000 : ℝ)*x 0 + (676581121/1250000000 : ℝ)*x 1 + (-30690473/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652803809/5000000000 : ℝ)^4299 ≤ (10879466168299/25000000000000 : ℝ)^3275 := by
    have hnat : (2652803809 : ℕ)^4299*25000000000000^3275 ≤ 10879466168299^3275*5000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652803809 5000000000 10879466168299 25000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (676581121/1250000000 : ℝ)^4299 ≤ (22336990534739/50000000000000 : ℝ)^3275 := by
    have hnat : (676581121 : ℕ)^4299*50000000000000^3275 ≤ 22336990534739^3275*1250000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      676581121 1250000000 22336990534739 50000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (30690473/156250000 : ℝ)^4299 ≤ (1476019279543/12500000000000 : ℝ)^3275 := by
    have hnat : (30690473 : ℕ)^4299*12500000000000^3275 ≤ 1476019279543^3275*156250000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      30690473 156250000 1476019279543 12500000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4299/1024 : ℝ)) 4299 3275 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652803809/5000000000 : ℝ), (676581121/1250000000 : ℝ), (-30690473/156250000 : ℝ)] ![(10879466168299/25000000000000 : ℝ), (22336990534739/50000000000000 : ℝ), (1476019279543/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652803809/5000000000 : ℝ)|^4299 ≤ (10879466168299/25000000000000 : ℝ)^3275
        have hw : |(2652803809/5000000000 : ℝ)|=(2652803809/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(676581121/1250000000 : ℝ)|^4299 ≤ (22336990534739/50000000000000 : ℝ)^3275
        have hw : |(676581121/1250000000 : ℝ)|=(676581121/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-30690473/156250000 : ℝ)|^4299 ≤ (1476019279543/12500000000000 : ℝ)^3275
        have hw : |(-30690473/156250000 : ℝ)|=(30690473/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1339_s5_7 (p : ℝ) (hpa : (2149/512 : ℝ) ≤ p) (hpb : p ≤ (4299/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1081850601/2500000000 : ℝ)*x 0 + (4506396371/10000000000 : ℝ)*x 1 + (4155131367/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1081850601/2500000000 : ℝ)^4299 ≤ (6660637884751/20000000000000 : ℝ)^3275 := by
    have hnat : (1081850601 : ℕ)^4299*20000000000000^3275 ≤ 6660637884751^3275*2500000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081850601 2500000000 6660637884751 20000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4506396371/10000000000 : ℝ)^4299 ≤ (3512300096331/10000000000000 : ℝ)^3275 := by
    have hnat : (4506396371 : ℕ)^4299*10000000000000^3275 ≤ 3512300096331^3275*10000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4506396371 10000000000 3512300096331 10000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4155131367/10000000000 : ℝ)^4299 ≤ (15786904799771/50000000000000 : ℝ)^3275 := by
    have hnat : (4155131367 : ℕ)^4299*50000000000000^3275 ≤ 15786904799771^3275*10000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4155131367 10000000000 15786904799771 50000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4299/1024 : ℝ)) 4299 3275 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1081850601/2500000000 : ℝ), (4506396371/10000000000 : ℝ), (4155131367/10000000000 : ℝ)] ![(6660637884751/20000000000000 : ℝ), (3512300096331/10000000000000 : ℝ), (15786904799771/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1081850601/2500000000 : ℝ)|^4299 ≤ (6660637884751/20000000000000 : ℝ)^3275
        have hw : |(1081850601/2500000000 : ℝ)|=(1081850601/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4506396371/10000000000 : ℝ)|^4299 ≤ (3512300096331/10000000000000 : ℝ)^3275
        have hw : |(4506396371/10000000000 : ℝ)|=(4506396371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4155131367/10000000000 : ℝ)|^4299 ≤ (15786904799771/50000000000000 : ℝ)^3275
        have hw : |(4155131367/10000000000 : ℝ)|=(4155131367/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1339_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2149/512 : ℝ) ≤ p) (hpb : p ≤ (4299/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77305211/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (369/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1109/10000 : ℝ)*pair X i i ≤ pair X i h) :
    (5567/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7357/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (369/2500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1109/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (369/2500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1109/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (369/2500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1109/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (369/2500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1109/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (369/2500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1109/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (369/2500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1109/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1109/10000 : ℝ) ^ (2149/512 : ℝ) ≤ (2450552537475711/25000000000000000000 : ℝ) := by
    have hpowers : (1109/10000 : ℝ)^2149 ≤ (2450552537475711/25000000000000000000 : ℝ)^512 := by
      have hnat : (1109 : ℕ)^2149*25000000000000000000^512 ≤ 2450552537475711^512*10000^2149 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1109 10000 2450552537475711 25000000000000000000 2149 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1109/10000 : ℝ)) (X := (2450552537475711/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2149 512 (by norm_num) hpowers
    exact h
  have hpowhi : (369/2500 : ℝ) ^ (2149/512 : ℝ) ≤ (8135321857802721/25000000000000000000 : ℝ) := by
    have hpowers : (369/2500 : ℝ)^2149 ≤ (8135321857802721/25000000000000000000 : ℝ)^512 := by
      have hnat : (369 : ℕ)^2149*25000000000000000000^512 ≤ 8135321857802721^512*2500^2149 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        369 2500 8135321857802721 25000000000000000000 2149 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (369/2500 : ℝ)) (X := (8135321857802721/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2149 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (12502450552537475711/12500000000000000000 : ℝ) ≤ (31251459503519/31250000000000 : ℝ) ^ (2149/512 : ℝ) := by
    have hpowers : (12502450552537475711/12500000000000000000 : ℝ)^512 ≤ (31251459503519/31250000000000 : ℝ)^2149 := by
      have hnat : (12502450552537475711 : ℕ)^512*31250000000000^2149 ≤ 31251459503519^2149*12500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12502450552537475711 12500000000000000000 31251459503519 31250000000000 512 2149 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (31251459503519/31250000000000 : ℝ)) (X := (12502450552537475711/12500000000000000000 : ℝ)) (by norm_num) 2149 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (781580808574852451/781250000000000000 : ℝ) ≤ (10001008672647459/10000000000000000 : ℝ) ^ (2149/512 : ℝ) := by
    have hpowers : (781580808574852451/781250000000000000 : ℝ)^512 ≤ (10001008672647459/10000000000000000 : ℝ)^2149 := by
      have hnat : (781580808574852451 : ℕ)^512*10000000000000000^2149 ≤ 10001008672647459^2149*781250000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        781580808574852451 781250000000000000 10001008672647459 10000000000000000 512 2149 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001008672647459/10000000000000000 : ℝ)) (X := (781580808574852451/781250000000000000 : ℝ)) (by norm_num) 2149 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (12508135321857802721/12500000000000000000 : ℝ) ≤ (5000775152084419/5000000000000000 : ℝ) ^ (2149/512 : ℝ) := by
    have hpowers : (12508135321857802721/12500000000000000000 : ℝ)^512 ≤ (5000775152084419/5000000000000000 : ℝ)^2149 := by
      have hnat : (12508135321857802721 : ℕ)^512*5000000000000000^2149 ≤ 5000775152084419^2149*12500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12508135321857802721 12500000000000000000 5000775152084419 5000000000000000 512 2149 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000775152084419/5000000000000000 : ℝ)) (X := (12508135321857802721/12500000000000000000 : ℝ)) (by norm_num) 2149 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2450552537475711/25000000000000000000 : ℝ) ≤ ((1834485032689426369/1835000000000000000 : ℝ)+2*(541631521379/367000000000000 : ℝ)*(1109/10000 : ℝ))^(2149/512 : ℝ) := by
    rw [show (1834485032689426369/1835000000000000000 : ℝ)+2*(541631521379/367000000000000 : ℝ)*(1109/10000 : ℝ)=(31251459503519/31250000000000 : ℝ) by norm_num, show 1+2*(2450552537475711/25000000000000000000 : ℝ)=(12502450552537475711/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(8135321857802721/25000000000000000000 : ℝ)+(2450552537475711/25000000000000000000 : ℝ) ≤ ((1834485032689426369/1835000000000000000 : ℝ)+(541631521379/367000000000000 : ℝ)*((369/2500 : ℝ)+(1109/10000 : ℝ)))^(2149/512 : ℝ) := by
    rw [show (1834485032689426369/1835000000000000000 : ℝ)+(541631521379/367000000000000 : ℝ)*((369/2500 : ℝ)+(1109/10000 : ℝ))=(10001008672647459/10000000000000000 : ℝ) by norm_num, show 1+(8135321857802721/25000000000000000000 : ℝ)+(2450552537475711/25000000000000000000 : ℝ)=(781580808574852451/781250000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(8135321857802721/25000000000000000000 : ℝ) ≤ ((1834485032689426369/1835000000000000000 : ℝ)+2*(541631521379/367000000000000 : ℝ)*(369/2500 : ℝ))^(2149/512 : ℝ) := by
    rw [show (1834485032689426369/1835000000000000000 : ℝ)+2*(541631521379/367000000000000 : ℝ)*(369/2500 : ℝ)=(5000775152084419/5000000000000000 : ℝ) by norm_num, show 1+2*(8135321857802721/25000000000000000000 : ℝ)=(12508135321857802721/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1834485032689426369/1835000000000000000 : ℝ)*(X 1 0+X 2 0)+(541631521379/367000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2149/512 : ℝ)) (lo := (1109/10000 : ℝ)) (hi := (369/2500 : ℝ)) (c := (1834485032689426369/1835000000000000000 : ℝ)) (alpha := (541631521379/367000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1834485032689426369/1835000000000000000 : ℝ)*(X 0 1+X 2 1)+(541631521379/367000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2149/512 : ℝ)) (lo := (1109/10000 : ℝ)) (hi := (369/2500 : ℝ)) (c := (1834485032689426369/1835000000000000000 : ℝ)) (alpha := (541631521379/367000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1834485032689426369/1835000000000000000 : ℝ)*(X 0 2+X 1 2)+(541631521379/367000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2149/512 : ℝ)) (lo := (1109/10000 : ℝ)) (hi := (369/2500 : ℝ)) (c := (1834485032689426369/1835000000000000000 : ℝ)) (alpha := (541631521379/367000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-409303447/2000000000 : ℝ)*X 0 0+(338328759/625000000 : ℝ)*X 0 1+(32775931/62500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1339_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((668643967/1250000000 : ℝ)*X 1 0+(-2132690293/10000000000 : ℝ)*X 1 1+(5244148961/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1339_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5349151751/10000000000 : ℝ)*X 2 0+(32775931/62500000 : ℝ)*X 2 1+(-2132690273/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1339_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2163688267/5000000000 : ℝ)*X 0 0+(4153852647/10000000000 : ℝ)*X 0 1+(880404/1953125 : ℝ)*X 0 2+(2163688267/5000000000 : ℝ)*X 1 0+(4153852647/10000000000 : ℝ)*X 1 1+(880404/1953125 : ℝ)*X 1 2+(2163688267/5000000000 : ℝ)*X 2 0+(4153852647/10000000000 : ℝ)*X 2 1+(880404/1953125 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1339_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2046529599/10000000000 : ℝ)*X 0 0+(1048951399/2000000000 : ℝ)*X 0 1+(541264897/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1339_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305607617/10000000000 : ℝ)*X 1 0+(-30690473/156250000 : ℝ)*X 1 1+(5412648969/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1339_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2652803809/5000000000 : ℝ)*X 2 0+(676581121/1250000000 : ℝ)*X 2 1+(-30690473/156250000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1339_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1081850601/2500000000 : ℝ)*X 0 0+(4506396371/10000000000 : ℝ)*X 0 1+(4155131367/10000000000 : ℝ)*X 0 2+(1081850601/2500000000 : ℝ)*X 1 0+(4506396371/10000000000 : ℝ)*X 1 1+(4155131367/10000000000 : ℝ)*X 1 2+(1081850601/2500000000 : ℝ)*X 2 0+(4506396371/10000000000 : ℝ)*X 2 1+(4155131367/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1339_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (229121775173540031810304533/45875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (479187207/50000000000000 : ℝ)*(base19) + (910488639/100000000000000 : ℝ)*(base23) + (34484791/100000000000000 : ℝ)*(lower2) + (59791419/50000000000000 : ℝ)*(upper3) + (12319003/12500000000000 : ℝ)*(upper5) + (4369828704562019/100000000000000 : ℝ)*(major0) + (4369828704562019/100000000000000 : ℝ)*(major1) + (4369828704562019/100000000000000 : ℝ)*(major2) + (5913289167644443/100000000000000 : ℝ)*(sp0) + (5913308197226589/100000000000000 : ℝ)*(sp1) + (1182661649022473/20000000000000 : ℝ)*(sp2) + (7065845648741/250000000000 : ℝ)*(sp3) + (19987956561/100000000000000 : ℝ)*(sp4) + (1965508791/20000000000000 : ℝ)*(sp7) + (1413174043520177/50000000000000 : ℝ)*(f.failure) + (1478327288900251/25000000000000 : ℝ)*(f.sum) + (98114674489601/18350000000000000000000000000 : ℝ)*base65 + (2436758764866515989/183500000000000000000000000000000 : ℝ)*base68 + (143375369057015989/183500000000000000000000000000000 : ℝ)*base70 + (2346113771038515989/183500000000000000000000000000000 : ℝ)*base72 + (5185939265401/18350000000000000000000000000 : ℝ)*base73 + (576623107696484011/183500000000000000000000000000000 : ℝ)*base75 + (1519775215157015989/183500000000000000000000000000000 : ℝ)*base78 + (1938008776652015989/183500000000000000000000000000000 : ℝ)*base80 + (50739349790201/18350000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (9257653/2500000000000000000000 : ℝ)*base90 + (9257653/2500000000000000000000 : ℝ)*base92 + (9257653/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (17262573432331663574667777/1835000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (327622273/20000000000000 : ℝ)*(base19) + (1782657911/100000000000000 : ℝ)*(base23) + (190569883/100000000000000 : ℝ)*(upper3) + (65141989/100000000000000 : ℝ)*(lower4) + (193047181/100000000000000 : ℝ)*(upper5) + (88030629168937/2000000000000 : ℝ)*(major0) + (88030629168937/2000000000000 : ℝ)*(major1) + (88030629168937/2000000000000 : ℝ)*(major2) + (16625924519/50000000000000 : ℝ)*(sp1) + (35767244149/100000000000000 : ℝ)*(sp2) + (2978104794727483/50000000000000 : ℝ)*(sp4) + (1489043674873641/25000000000000 : ℝ)*(sp5) + (2978086019776453/50000000000000 : ℝ)*(sp6) + (2846853013858827/100000000000000 : ℝ)*(sp7) + (2846853013858827/100000000000000 : ℝ)*(f.failure) + (2978104794727483/50000000000000 : ℝ)*(f.sum) + (450680340633/73400000000000000000000000 : ℝ)*base65 + (59236270888175247/3670000000000000000000000000000 : ℝ)*base68 + (38855687567315247/3670000000000000000000000000000 : ℝ)*base70 + (23840735970765247/3670000000000000000000000000000 : ℝ)*base72 + (717394472901/183500000000000000000000000 : ℝ)*base74 + (24289343848695247/3670000000000000000000000000000 : ℝ)*base76 + (30517819653935247/3670000000000000000000000000000 : ℝ)*base78 + (10501419270435247/3670000000000000000000000000000 : ℝ)*base80 + (449724446323/367000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (45447497/5000000000000000000000 : ℝ)*base89 + (45447497/5000000000000000000000 : ℝ)*base91 + (45447497/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1339_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2149/512 : ℝ) ≤ p) (hpb : p ≤ (4299/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77305211/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (369/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1109/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5567/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7357/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1339_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1339_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2149/512 : ℝ) ≤ p) (hpb : p ≤ (4299/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77305211/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4029/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1229/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5567/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7357/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1339_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1339_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1339_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2149/512 : ℝ) ≤ p) (hpb : p ≤ (4299/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77305211/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4029/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1229/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5567/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7357/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1339_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
