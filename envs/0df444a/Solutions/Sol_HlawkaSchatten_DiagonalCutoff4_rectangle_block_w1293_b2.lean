-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1293_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:26:58.641105+00:00
-- url     : https://prove2.me/submissions/dd48681a-4be1-4a20-8e54-142052a2401b

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
theorem support_rectangle_w1293_s6_0 (p : ℝ) (hpa : (1063/256 : ℝ) ≤ p) (hpb : p ≤ (4253/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-208706397/1000000000 : ℝ)*x 0 + (1083054141/2000000000 : ℝ)*x 1 + (5242942371/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (208706397/1000000000 : ℝ)^4253 ≤ (12698219430363/100000000000000 : ℝ)^3229 := by
    have hnat : (208706397 : ℕ)^4253*100000000000000^3229 ≤ 12698219430363^3229*1000000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      208706397 1000000000 12698219430363 100000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1083054141/2000000000 : ℝ)^4253 ≤ (11145105879677/25000000000000 : ℝ)^3229 := by
    have hnat : (1083054141 : ℕ)^4253*25000000000000^3229 ≤ 11145105879677^3229*2000000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083054141 2000000000 11145105879677 25000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5242942371/10000000000 : ℝ)^4253 ≤ (21360678518391/50000000000000 : ℝ)^3229 := by
    have hnat : (5242942371 : ℕ)^4253*50000000000000^3229 ≤ 21360678518391^3229*10000000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242942371 10000000000 21360678518391 50000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4253/1024 : ℝ)) 4253 3229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-208706397/1000000000 : ℝ), (1083054141/2000000000 : ℝ), (5242942371/10000000000 : ℝ)] ![(12698219430363/100000000000000 : ℝ), (11145105879677/25000000000000 : ℝ), (21360678518391/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-208706397/1000000000 : ℝ)|^4253 ≤ (12698219430363/100000000000000 : ℝ)^3229
        have hw : |(-208706397/1000000000 : ℝ)|=(208706397/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1083054141/2000000000 : ℝ)|^4253 ≤ (11145105879677/25000000000000 : ℝ)^3229
        have hw : |(1083054141/2000000000 : ℝ)|=(1083054141/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5242942371/10000000000 : ℝ)|^4253 ≤ (21360678518391/50000000000000 : ℝ)^3229
        have hw : |(5242942371/10000000000 : ℝ)|=(5242942371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1293_s6_1 (p : ℝ) (hpa : (1063/256 : ℝ) ≤ p) (hpb : p ≤ (4253/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349792697/10000000000 : ℝ)*x 0 + (-16991473/78125000 : ℝ)*x 1 + (5242942371/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349792697/10000000000 : ℝ)^4253 ≤ (2193590367331/5000000000000 : ℝ)^3229 := by
    have hnat : (5349792697 : ℕ)^4253*5000000000000^3229 ≤ 2193590367331^3229*10000000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349792697 10000000000 2193590367331 5000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (16991473/78125000 : ℝ)^4253 ≤ (2681367119153/20000000000000 : ℝ)^3229 := by
    have hnat : (16991473 : ℕ)^4253*20000000000000^3229 ≤ 2681367119153^3229*78125000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16991473 78125000 2681367119153 20000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5242942371/10000000000 : ℝ)^4253 ≤ (21360678518391/50000000000000 : ℝ)^3229 := by
    have hnat : (5242942371 : ℕ)^4253*50000000000000^3229 ≤ 21360678518391^3229*10000000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242942371 10000000000 21360678518391 50000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4253/1024 : ℝ)) 4253 3229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349792697/10000000000 : ℝ), (-16991473/78125000 : ℝ), (5242942371/10000000000 : ℝ)] ![(2193590367331/5000000000000 : ℝ), (2681367119153/20000000000000 : ℝ), (21360678518391/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349792697/10000000000 : ℝ)|^4253 ≤ (2193590367331/5000000000000 : ℝ)^3229
        have hw : |(5349792697/10000000000 : ℝ)|=(5349792697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-16991473/78125000 : ℝ)|^4253 ≤ (2681367119153/20000000000000 : ℝ)^3229
        have hw : |(-16991473/78125000 : ℝ)|=(16991473/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5242942371/10000000000 : ℝ)|^4253 ≤ (21360678518391/50000000000000 : ℝ)^3229
        have hw : |(5242942371/10000000000 : ℝ)|=(5242942371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1293_s6_2 (p : ℝ) (hpa : (1063/256 : ℝ) ≤ p) (hpb : p ≤ (4253/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349792699/10000000000 : ℝ)*x 0 + (5242942369/10000000000 : ℝ)*x 1 + (-434981709/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349792699/10000000000 : ℝ)^4253 ≤ (43871807368223/100000000000000 : ℝ)^3229 := by
    have hnat : (5349792699 : ℕ)^4253*100000000000000^3229 ≤ 43871807368223^3229*10000000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349792699 10000000000 43871807368223 100000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5242942369/10000000000 : ℝ)^4253 ≤ (42721357015317/100000000000000 : ℝ)^3229 := by
    have hnat : (5242942369 : ℕ)^4253*100000000000000^3229 ≤ 42721357015317^3229*10000000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242942369 10000000000 42721357015317 100000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (434981709/2000000000 : ℝ)^4253 ≤ (3351708900971/25000000000000 : ℝ)^3229 := by
    have hnat : (434981709 : ℕ)^4253*25000000000000^3229 ≤ 3351708900971^3229*2000000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      434981709 2000000000 3351708900971 25000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4253/1024 : ℝ)) 4253 3229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349792699/10000000000 : ℝ), (5242942369/10000000000 : ℝ), (-434981709/2000000000 : ℝ)] ![(43871807368223/100000000000000 : ℝ), (42721357015317/100000000000000 : ℝ), (3351708900971/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349792699/10000000000 : ℝ)|^4253 ≤ (43871807368223/100000000000000 : ℝ)^3229
        have hw : |(5349792699/10000000000 : ℝ)|=(5349792699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5242942369/10000000000 : ℝ)|^4253 ≤ (42721357015317/100000000000000 : ℝ)^3229
        have hw : |(5242942369/10000000000 : ℝ)|=(5242942369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-434981709/2000000000 : ℝ)|^4253 ≤ (3351708900971/25000000000000 : ℝ)^3229
        have hw : |(-434981709/2000000000 : ℝ)|=(434981709/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1293_s6_3 (p : ℝ) (hpa : (1063/256 : ℝ) ≤ p) (hpb : p ≤ (4253/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4339592391/10000000000 : ℝ)*x 0 + (2082945937/5000000000 : ℝ)*x 1 + (904040563/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4339592391/10000000000 : ℝ)^4253 ≤ (16651162502999/50000000000000 : ℝ)^3229 := by
    have hnat : (4339592391 : ℕ)^4253*50000000000000^3229 ≤ 16651162502999^3229*10000000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4339592391 10000000000 16651162502999 50000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2082945937/5000000000 : ℝ)^4253 ≤ (31557856252237/100000000000000 : ℝ)^3229 := by
    have hnat : (2082945937 : ℕ)^4253*100000000000000^3229 ≤ 31557856252237^3229*5000000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2082945937 5000000000 31557856252237 100000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (904040563/2000000000 : ℝ)^4253 ≤ (7027963745533/20000000000000 : ℝ)^3229 := by
    have hnat : (904040563 : ℕ)^4253*20000000000000^3229 ≤ 7027963745533^3229*2000000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      904040563 2000000000 7027963745533 20000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4253/1024 : ℝ)) 4253 3229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4339592391/10000000000 : ℝ), (2082945937/5000000000 : ℝ), (904040563/2000000000 : ℝ)] ![(16651162502999/50000000000000 : ℝ), (31557856252237/100000000000000 : ℝ), (7027963745533/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4339592391/10000000000 : ℝ)|^4253 ≤ (16651162502999/50000000000000 : ℝ)^3229
        have hw : |(4339592391/10000000000 : ℝ)|=(4339592391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2082945937/5000000000 : ℝ)|^4253 ≤ (31557856252237/100000000000000 : ℝ)^3229
        have hw : |(2082945937/5000000000 : ℝ)|=(2082945937/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(904040563/2000000000 : ℝ)|^4253 ≤ (7027963745533/20000000000000 : ℝ)^3229
        have hw : |(904040563/2000000000 : ℝ)|=(904040563/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1293_s6_4 (p : ℝ) (hpa : (1063/256 : ℝ) ≤ p) (hpb : p ≤ (4253/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-26088463/125000000 : ℝ)*x 0 + (5243557191/10000000000 : ℝ)*x 1 + (1353663119/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (26088463/125000000 : ℝ)^4253 ≤ (2539664833969/20000000000000 : ℝ)^3229 := by
    have hnat : (26088463 : ℕ)^4253*20000000000000^3229 ≤ 2539664833969^3229*125000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26088463 125000000 2539664833969 20000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5243557191/10000000000 : ℝ)^4253 ≤ (10681988915091/25000000000000 : ℝ)^3229 := by
    have hnat : (5243557191 : ℕ)^4253*25000000000000^3229 ≤ 10681988915091^3229*10000000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243557191 10000000000 10681988915091 25000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1353663119/2500000000 : ℝ)^4253 ≤ (4457372015371/10000000000000 : ℝ)^3229 := by
    have hnat : (1353663119 : ℕ)^4253*10000000000000^3229 ≤ 4457372015371^3229*2500000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1353663119 2500000000 4457372015371 10000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4253/1024 : ℝ)) 4253 3229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-26088463/125000000 : ℝ), (5243557191/10000000000 : ℝ), (1353663119/2500000000 : ℝ)] ![(2539664833969/20000000000000 : ℝ), (10681988915091/25000000000000 : ℝ), (4457372015371/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-26088463/125000000 : ℝ)|^4253 ≤ (2539664833969/20000000000000 : ℝ)^3229
        have hw : |(-26088463/125000000 : ℝ)|=(26088463/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5243557191/10000000000 : ℝ)|^4253 ≤ (10681988915091/25000000000000 : ℝ)^3229
        have hw : |(5243557191/10000000000 : ℝ)|=(5243557191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1353663119/2500000000 : ℝ)|^4253 ≤ (4457372015371/10000000000000 : ℝ)^3229
        have hw : |(1353663119/2500000000 : ℝ)|=(1353663119/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1293_s6_5 (p : ℝ) (hpa : (1063/256 : ℝ) ≤ p) (hpb : p ≤ (4253/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305666451/10000000000 : ℝ)*x 0 + (-250399781/1250000000 : ℝ)*x 1 + (2707326419/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305666451/10000000000 : ℝ)^4253 ≤ (43395811184167/100000000000000 : ℝ)^3229 := by
    have hnat : (5305666451 : ℕ)^4253*100000000000000^3229 ≤ 43395811184167^3229*10000000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305666451 10000000000 43395811184167 100000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (250399781/1250000000 : ℝ)^4253 ≤ (6015232357713/50000000000000 : ℝ)^3229 := by
    have hnat : (250399781 : ℕ)^4253*50000000000000^3229 ≤ 6015232357713^3229*1250000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      250399781 1250000000 6015232357713 50000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2707326419/5000000000 : ℝ)^4253 ≤ (44573724078751/100000000000000 : ℝ)^3229 := by
    have hnat : (2707326419 : ℕ)^4253*100000000000000^3229 ≤ 44573724078751^3229*5000000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2707326419 5000000000 44573724078751 100000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4253/1024 : ℝ)) 4253 3229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305666451/10000000000 : ℝ), (-250399781/1250000000 : ℝ), (2707326419/5000000000 : ℝ)] ![(43395811184167/100000000000000 : ℝ), (6015232357713/50000000000000 : ℝ), (44573724078751/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305666451/10000000000 : ℝ)|^4253 ≤ (43395811184167/100000000000000 : ℝ)^3229
        have hw : |(5305666451/10000000000 : ℝ)|=(5305666451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-250399781/1250000000 : ℝ)|^4253 ≤ (6015232357713/50000000000000 : ℝ)^3229
        have hw : |(-250399781/1250000000 : ℝ)|=(250399781/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2707326419/5000000000 : ℝ)|^4253 ≤ (44573724078751/100000000000000 : ℝ)^3229
        have hw : |(2707326419/5000000000 : ℝ)|=(2707326419/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1293_s6_6 (p : ℝ) (hpa : (1063/256 : ℝ) ≤ p) (hpb : p ≤ (4253/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (663208351/1250000000 : ℝ)*x 0 + (2707326271/5000000000 : ℝ)*x 1 + (-250399771/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (663208351/1250000000 : ℝ)^4253 ≤ (8679163006023/20000000000000 : ℝ)^3229 := by
    have hnat : (663208351 : ℕ)^4253*20000000000000^3229 ≤ 8679163006023^3229*1250000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      663208351 1250000000 8679163006023 20000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2707326271/5000000000 : ℝ)^4253 ≤ (1782948834773/4000000000000 : ℝ)^3229 := by
    have hnat : (2707326271 : ℕ)^4253*4000000000000^3229 ≤ 1782948834773^3229*5000000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2707326271 5000000000 1782948834773 4000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (250399771/1250000000 : ℝ)^4253 ≤ (12030464082613/100000000000000 : ℝ)^3229 := by
    have hnat : (250399771 : ℕ)^4253*100000000000000^3229 ≤ 12030464082613^3229*1250000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      250399771 1250000000 12030464082613 100000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4253/1024 : ℝ)) 4253 3229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(663208351/1250000000 : ℝ), (2707326271/5000000000 : ℝ), (-250399771/1250000000 : ℝ)] ![(8679163006023/20000000000000 : ℝ), (1782948834773/4000000000000 : ℝ), (12030464082613/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(663208351/1250000000 : ℝ)|^4253 ≤ (8679163006023/20000000000000 : ℝ)^3229
        have hw : |(663208351/1250000000 : ℝ)|=(663208351/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2707326271/5000000000 : ℝ)|^4253 ≤ (1782948834773/4000000000000 : ℝ)^3229
        have hw : |(2707326271/5000000000 : ℝ)|=(2707326271/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-250399771/1250000000 : ℝ)|^4253 ≤ (12030464082613/100000000000000 : ℝ)^3229
        have hw : |(-250399771/1250000000 : ℝ)|=(250399771/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1293_s6_7 (p : ℝ) (hpa : (1063/256 : ℝ) ≤ p) (hpb : p ≤ (4253/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4339619033/10000000000 : ℝ)*x 0 + (564867297/1250000000 : ℝ)*x 1 + (4167162363/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4339619033/10000000000 : ℝ)^4253 ≤ (16651297147991/50000000000000 : ℝ)^3229 := by
    have hnat : (4339619033 : ℕ)^4253*50000000000000^3229 ≤ 16651297147991^3229*10000000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4339619033 10000000000 16651297147991 50000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (564867297/1250000000 : ℝ)^4253 ≤ (35126872371491/100000000000000 : ℝ)^3229 := by
    have hnat : (564867297 : ℕ)^4253*100000000000000^3229 ≤ 35126872371491^3229*1250000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      564867297 1250000000 35126872371491 100000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4167162363/10000000000 : ℝ)^4253 ≤ (31570533318091/100000000000000 : ℝ)^3229 := by
    have hnat : (4167162363 : ℕ)^4253*100000000000000^3229 ≤ 31570533318091^3229*10000000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4167162363 10000000000 31570533318091 100000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4253/1024 : ℝ)) 4253 3229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4339619033/10000000000 : ℝ), (564867297/1250000000 : ℝ), (4167162363/10000000000 : ℝ)] ![(16651297147991/50000000000000 : ℝ), (35126872371491/100000000000000 : ℝ), (31570533318091/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4339619033/10000000000 : ℝ)|^4253 ≤ (16651297147991/50000000000000 : ℝ)^3229
        have hw : |(4339619033/10000000000 : ℝ)|=(4339619033/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(564867297/1250000000 : ℝ)|^4253 ≤ (35126872371491/100000000000000 : ℝ)^3229
        have hw : |(564867297/1250000000 : ℝ)|=(564867297/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4167162363/10000000000 : ℝ)|^4253 ≤ (31570533318091/100000000000000 : ℝ)^3229
        have hw : |(4167162363/10000000000 : ℝ)|=(4167162363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1293_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1063/256 : ℝ) ≤ p) (hpb : p ≤ (4253/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76400563/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14687/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11017/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2757/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (587/4000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14687/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11017/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14687/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11017/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14687/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11017/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14687/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11017/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14687/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11017/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14687/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11017/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11017/100000 : ℝ) ^ (1063/256 : ℝ) ≤ (1315914732420537/12500000000000000000 : ℝ) := by
    have hpowers : (11017/100000 : ℝ)^1063 ≤ (1315914732420537/12500000000000000000 : ℝ)^256 := by
      have hnat : (11017 : ℕ)^1063*12500000000000000000^256 ≤ 1315914732420537^256*100000^1063 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11017 100000 1315914732420537 12500000000000000000 1063 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11017/100000 : ℝ)) (X := (1315914732420537/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 1063 256 (by norm_num) hpowers
    exact h
  have hpowhi : (14687/100000 : ℝ) ^ (1063/256 : ℝ) ≤ (34739202414481647/100000000000000000000 : ℝ) := by
    have hpowers : (14687/100000 : ℝ)^1063 ≤ (34739202414481647/100000000000000000000 : ℝ)^256 := by
      have hnat : (14687 : ℕ)^1063*100000000000000000000^256 ≤ 34739202414481647^256*100000^1063 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14687 100000 34739202414481647 100000000000000000000 1063 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14687/100000 : ℝ)) (X := (34739202414481647/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1063 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (6251315914732420537/6250000000000000000 : ℝ) ≤ (5000253506868623/5000000000000000 : ℝ) ^ (1063/256 : ℝ) := by
    have hpowers : (6251315914732420537/6250000000000000000 : ℝ)^256 ≤ (5000253506868623/5000000000000000 : ℝ)^1063 := by
      have hnat : (6251315914732420537 : ℕ)^256*5000000000000000^1063 ≤ 5000253506868623^1063*6250000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6251315914732420537 6250000000000000000 5000253506868623 5000000000000000 256 1063 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000253506868623/5000000000000000 : ℝ)) (X := (6251315914732420537/6250000000000000000 : ℝ)) (by norm_num) 1063 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (100045266520273845943/100000000000000000000 : ℝ) ≤ (1000108995659137/1000000000000000 : ℝ) ^ (1063/256 : ℝ) := by
    have hpowers : (100045266520273845943/100000000000000000000 : ℝ)^256 ≤ (1000108995659137/1000000000000000 : ℝ)^1063 := by
      have hnat : (100045266520273845943 : ℕ)^256*1000000000000000^1063 ≤ 1000108995659137^1063*100000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100045266520273845943 100000000000000000000 1000108995659137 1000000000000000 256 1063 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000108995659137/1000000000000000 : ℝ)) (X := (100045266520273845943/100000000000000000000 : ℝ)) (by norm_num) 1063 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (50034739202414481647/50000000000000000000 : ℝ) ≤ (5000836449722747/5000000000000000 : ℝ) ^ (1063/256 : ℝ) := by
    have hpowers : (50034739202414481647/50000000000000000000 : ℝ)^256 ≤ (5000836449722747/5000000000000000 : ℝ)^1063 := by
      have hnat : (50034739202414481647 : ℕ)^256*5000000000000000^1063 ≤ 5000836449722747^1063*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50034739202414481647 50000000000000000000 5000836449722747 5000000000000000 256 1063 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000836449722747/5000000000000000 : ℝ)) (X := (50034739202414481647/50000000000000000000 : ℝ)) (by norm_num) 1063 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1315914732420537/12500000000000000000 : ℝ) ≤ ((9172254044391981151/9175000000000000000 : ℝ)+2*(145735713531/91750000000000 : ℝ)*(11017/100000 : ℝ))^(1063/256 : ℝ) := by
    rw [show (9172254044391981151/9175000000000000000 : ℝ)+2*(145735713531/91750000000000 : ℝ)*(11017/100000 : ℝ)=(5000253506868623/5000000000000000 : ℝ) by norm_num, show 1+2*(1315914732420537/12500000000000000000 : ℝ)=(6251315914732420537/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(34739202414481647/100000000000000000000 : ℝ)+(1315914732420537/12500000000000000000 : ℝ) ≤ ((9172254044391981151/9175000000000000000 : ℝ)+(145735713531/91750000000000 : ℝ)*((14687/100000 : ℝ)+(11017/100000 : ℝ)))^(1063/256 : ℝ) := by
    rw [show (9172254044391981151/9175000000000000000 : ℝ)+(145735713531/91750000000000 : ℝ)*((14687/100000 : ℝ)+(11017/100000 : ℝ))=(1000108995659137/1000000000000000 : ℝ) by norm_num, show 1+(34739202414481647/100000000000000000000 : ℝ)+(1315914732420537/12500000000000000000 : ℝ)=(100045266520273845943/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(34739202414481647/100000000000000000000 : ℝ) ≤ ((9172254044391981151/9175000000000000000 : ℝ)+2*(145735713531/91750000000000 : ℝ)*(14687/100000 : ℝ))^(1063/256 : ℝ) := by
    rw [show (9172254044391981151/9175000000000000000 : ℝ)+2*(145735713531/91750000000000 : ℝ)*(14687/100000 : ℝ)=(5000836449722747/5000000000000000 : ℝ) by norm_num, show 1+2*(34739202414481647/100000000000000000000 : ℝ)=(50034739202414481647/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (9172254044391981151/9175000000000000000 : ℝ)*(X 1 0+X 2 0)+(145735713531/91750000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1063/256 : ℝ)) (lo := (11017/100000 : ℝ)) (hi := (14687/100000 : ℝ)) (c := (9172254044391981151/9175000000000000000 : ℝ)) (alpha := (145735713531/91750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (9172254044391981151/9175000000000000000 : ℝ)*(X 0 1+X 2 1)+(145735713531/91750000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1063/256 : ℝ)) (lo := (11017/100000 : ℝ)) (hi := (14687/100000 : ℝ)) (c := (9172254044391981151/9175000000000000000 : ℝ)) (alpha := (145735713531/91750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (9172254044391981151/9175000000000000000 : ℝ)*(X 0 2+X 1 2)+(145735713531/91750000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1063/256 : ℝ)) (lo := (11017/100000 : ℝ)) (hi := (14687/100000 : ℝ)) (c := (9172254044391981151/9175000000000000000 : ℝ)) (alpha := (145735713531/91750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-208706397/1000000000 : ℝ)*X 0 0+(1083054141/2000000000 : ℝ)*X 0 1+(5242942371/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1293_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5349792697/10000000000 : ℝ)*X 1 0+(-16991473/78125000 : ℝ)*X 1 1+(5242942371/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1293_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5349792699/10000000000 : ℝ)*X 2 0+(5242942369/10000000000 : ℝ)*X 2 1+(-434981709/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1293_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4339592391/10000000000 : ℝ)*X 0 0+(2082945937/5000000000 : ℝ)*X 0 1+(904040563/2000000000 : ℝ)*X 0 2+(4339592391/10000000000 : ℝ)*X 1 0+(2082945937/5000000000 : ℝ)*X 1 1+(904040563/2000000000 : ℝ)*X 1 2+(4339592391/10000000000 : ℝ)*X 2 0+(2082945937/5000000000 : ℝ)*X 2 1+(904040563/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1293_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-26088463/125000000 : ℝ)*X 0 0+(5243557191/10000000000 : ℝ)*X 0 1+(1353663119/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1293_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305666451/10000000000 : ℝ)*X 1 0+(-250399781/1250000000 : ℝ)*X 1 1+(2707326419/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1293_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((663208351/1250000000 : ℝ)*X 2 0+(2707326271/5000000000 : ℝ)*X 2 1+(-250399771/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1293_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4339619033/10000000000 : ℝ)*X 0 0+(564867297/1250000000 : ℝ)*X 0 1+(4167162363/10000000000 : ℝ)*X 0 2+(4339619033/10000000000 : ℝ)*X 1 0+(564867297/1250000000 : ℝ)*X 1 1+(4167162363/10000000000 : ℝ)*X 1 2+(4339619033/10000000000 : ℝ)*X 2 0+(564867297/1250000000 : ℝ)*X 2 1+(4167162363/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1293_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (874547681679326308366005663/114687500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (730099199/50000000000000 : ℝ)*(base19) + (1362258831/100000000000000 : ℝ)*(base23) + (52301/97656250000 : ℝ)*(lower2) + (19276919/10000000000000 : ℝ)*(upper3) + (118065491/100000000000000 : ℝ)*(upper5) + (1078168158586071/25000000000000 : ℝ)*(major0) + (1078168158586071/25000000000000 : ℝ)*(major1) + (1078168158586071/25000000000000 : ℝ)*(major2) + (72536335646471/1250000000000 : ℝ)*(sp0) + (5802934618430623/100000000000000 : ℝ)*(sp1) + (580293471637019/10000000000000 : ℝ)*(sp2) + (705598376731173/25000000000000 : ℝ)*(sp3) + (29226911341/100000000000000 : ℝ)*(sp4) + (15428952053/100000000000000 : ℝ)*(sp7) + (564481787175349/20000000000000 : ℝ)*(f.failure) + (290146803931451/5000000000000 : ℝ)*(f.sum) + (5412459845433/9175000000000000000000000000 : ℝ)*base65 + (682500912179877279/229375000000000000000000000000000 : ℝ)*base68 + (892839122122622721/229375000000000000000000000000000 : ℝ)*base69 + (1977745085573247721/229375000000000000000000000000000 : ℝ)*base71 + (3755830821449/1146875000000000000000000000 : ℝ)*base74 + (2288747537926752279/229375000000000000000000000000000 : ℝ)*base76 + (251018980984877279/229375000000000000000000000000000 : ℝ)*base78 + (1321313172488002279/229375000000000000000000000000000 : ℝ)*base80 + (26050956350533/9175000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (3321487/1000000000000000000000 : ℝ)*base89 + (3321487/1000000000000000000000 : ℝ)*base91 + (3321487/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (18563002070208857435229/9175000000000000000000000000 : ℝ) := by norm_num
    linear_combination (885561129/100000000000000 : ℝ)*(base19) + (1443142653/100000000000000 : ℝ)*(base23) + (5086077/10000000000000 : ℝ)*(upper2) + (376157/160000000000 : ℝ)*(upper3) + (22206667/12500000000000 : ℝ)*(upper5) + (4343708334093037/100000000000000 : ℝ)*(major0) + (4343708334093037/100000000000000 : ℝ)*(major1) + (4343708334093037/100000000000000 : ℝ)*(major2) + (4455644623/20000000000000 : ℝ)*(sp1) + (30508893429/100000000000000 : ℝ)*(sp2) + (730587061589871/12500000000000 : ℝ)*(sp4) + (1461168332233681/25000000000000 : ℝ)*(sp5) + (2922332270341443/50000000000000 : ℝ)*(sp6) + (355340013503323/12500000000000 : ℝ)*(sp7) + (355340013503323/12500000000000 : ℝ)*(f.failure) + (730587061589871/12500000000000 : ℝ)*(f.sum) + (1843860926347/4587500000000000000000000000 : ℝ)*base65 + (342628000510954413/917500000000000000000000000000000 : ℝ)*base68 + (3565338205249045587/917500000000000000000000000000000 : ℝ)*base69 + (4634621874993454413/917500000000000000000000000000000 : ℝ)*base72 + (17534253580847/4587500000000000000000000000 : ℝ)*base73 + (8157345323991545587/917500000000000000000000000000000 : ℝ)*base75 + (4155491520893454413/917500000000000000000000000000000 : ℝ)*base78 + (11119616351051545587/917500000000000000000000000000000 : ℝ)*base79 + (55007389006969/9175000000000000000000000000 : ℝ)*base81 + (1679151/625000000000000000000 : ℝ)*base90 + (1679151/625000000000000000000 : ℝ)*base92 + (1679151/625000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1293_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1063/256 : ℝ) ≤ p) (hpb : p ≤ (4253/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76400563/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14687/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11017/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2757/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (587/4000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1293_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1293_s7_0 (p : ℝ) (hpa : (1063/256 : ℝ) ≤ p) (hpb : p ≤ (4253/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-130442341/625000000 : ℝ)*x 0 + (5415166757/10000000000 : ℝ)*x 1 + (131075933/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (130442341/625000000 : ℝ)^4253 ≤ (12698327503561/100000000000000 : ℝ)^3229 := by
    have hnat : (130442341 : ℕ)^4253*100000000000000^3229 ≤ 12698327503561^3229*625000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      130442341 625000000 12698327503561 100000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5415166757/10000000000 : ℝ)^4253 ≤ (5572412051131/12500000000000 : ℝ)^3229 := by
    have hnat : (5415166757 : ℕ)^4253*12500000000000^3229 ≤ 5572412051131^3229*10000000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5415166757 10000000000 5572412051131 12500000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (131075933/250000000 : ℝ)^4253 ≤ (21361188035697/50000000000000 : ℝ)^3229 := by
    have hnat : (131075933 : ℕ)^4253*50000000000000^3229 ≤ 21361188035697^3229*250000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131075933 250000000 21361188035697 50000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4253/1024 : ℝ)) 4253 3229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-130442341/625000000 : ℝ), (5415166757/10000000000 : ℝ), (131075933/250000000 : ℝ)] ![(12698327503561/100000000000000 : ℝ), (5572412051131/12500000000000 : ℝ), (21361188035697/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-130442341/625000000 : ℝ)|^4253 ≤ (12698327503561/100000000000000 : ℝ)^3229
        have hw : |(-130442341/625000000 : ℝ)|=(130442341/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5415166757/10000000000 : ℝ)|^4253 ≤ (5572412051131/12500000000000 : ℝ)^3229
        have hw : |(5415166757/10000000000 : ℝ)|=(5415166757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(131075933/250000000 : ℝ)|^4253 ≤ (21361188035697/50000000000000 : ℝ)^3229
        have hw : |(131075933/250000000 : ℝ)|=(131075933/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1293_s7_1 (p : ℝ) (hpa : (1063/256 : ℝ) ≤ p) (hpb : p ≤ (4253/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (267488303/500000000 : ℝ)*x 0 + (-1087409473/5000000000 : ℝ)*x 1 + (5243036961/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267488303/500000000 : ℝ)^4253 ≤ (43871519632697/100000000000000 : ℝ)^3229 := by
    have hnat : (267488303 : ℕ)^4253*100000000000000^3229 ≤ 43871519632697^3229*500000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267488303 500000000 43871519632697 100000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1087409473/5000000000 : ℝ)^4253 ≤ (1340610813747/10000000000000 : ℝ)^3229 := by
    have hnat : (1087409473 : ℕ)^4253*10000000000000^3229 ≤ 1340610813747^3229*5000000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1087409473 5000000000 1340610813747 10000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5243036961/10000000000 : ℝ)^4253 ≤ (42722372218437/100000000000000 : ℝ)^3229 := by
    have hnat : (5243036961 : ℕ)^4253*100000000000000^3229 ≤ 42722372218437^3229*10000000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243036961 10000000000 42722372218437 100000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4253/1024 : ℝ)) 4253 3229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(267488303/500000000 : ℝ), (-1087409473/5000000000 : ℝ), (5243036961/10000000000 : ℝ)] ![(43871519632697/100000000000000 : ℝ), (1340610813747/10000000000000 : ℝ), (42722372218437/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(267488303/500000000 : ℝ)|^4253 ≤ (43871519632697/100000000000000 : ℝ)^3229
        have hw : |(267488303/500000000 : ℝ)|=(267488303/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1087409473/5000000000 : ℝ)|^4253 ≤ (1340610813747/10000000000000 : ℝ)^3229
        have hw : |(-1087409473/5000000000 : ℝ)|=(1087409473/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5243036961/10000000000 : ℝ)|^4253 ≤ (42722372218437/100000000000000 : ℝ)^3229
        have hw : |(5243036961/10000000000 : ℝ)|=(5243036961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1293_s7_2 (p : ℝ) (hpa : (1063/256 : ℝ) ≤ p) (hpb : p ≤ (4253/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2674882821/5000000000 : ℝ)*x 0 + (5243039241/10000000000 : ℝ)*x 1 + (-2174816487/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674882821/5000000000 : ℝ)^4253 ≤ (21935757558881/50000000000000 : ℝ)^3229 := by
    have hnat : (2674882821 : ℕ)^4253*50000000000000^3229 ≤ 21935757558881^3229*5000000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674882821 5000000000 21935757558881 50000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5243039241/10000000000 : ℝ)^4253 ≤ (1708895867539/4000000000000 : ℝ)^3229 := by
    have hnat : (5243039241 : ℕ)^4253*4000000000000^3229 ≤ 1708895867539^3229*10000000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243039241 10000000000 1708895867539 4000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2174816487/10000000000 : ℝ)^4253 ≤ (268121763453/2000000000000 : ℝ)^3229 := by
    have hnat : (2174816487 : ℕ)^4253*2000000000000^3229 ≤ 268121763453^3229*10000000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2174816487 10000000000 268121763453 2000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4253/1024 : ℝ)) 4253 3229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674882821/5000000000 : ℝ), (5243039241/10000000000 : ℝ), (-2174816487/10000000000 : ℝ)] ![(21935757558881/50000000000000 : ℝ), (1708895867539/4000000000000 : ℝ), (268121763453/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674882821/5000000000 : ℝ)|^4253 ≤ (21935757558881/50000000000000 : ℝ)^3229
        have hw : |(2674882821/5000000000 : ℝ)|=(2674882821/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5243039241/10000000000 : ℝ)|^4253 ≤ (1708895867539/4000000000000 : ℝ)^3229
        have hw : |(5243039241/10000000000 : ℝ)|=(5243039241/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2174816487/10000000000 : ℝ)|^4253 ≤ (268121763453/2000000000000 : ℝ)^3229
        have hw : |(-2174816487/10000000000 : ℝ)|=(2174816487/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1293_s7_3 (p : ℝ) (hpa : (1063/256 : ℝ) ≤ p) (hpb : p ≤ (4253/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4339601187/10000000000 : ℝ)*x 0 + (4166095617/10000000000 : ℝ)*x 1 + (564999449/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4339601187/10000000000 : ℝ)^4253 ≤ (832560347837/2500000000000 : ℝ)^3229 := by
    have hnat : (4339601187 : ℕ)^4253*2500000000000^3229 ≤ 832560347837^3229*10000000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4339601187 10000000000 832560347837 2500000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4166095617/10000000000 : ℝ)^4253 ≤ (15779944568831/50000000000000 : ℝ)^3229 := by
    have hnat : (4166095617 : ℕ)^4253*50000000000000^3229 ≤ 15779944568831^3229*10000000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4166095617 10000000000 15779944568831 50000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (564999449/1250000000 : ℝ)^4253 ≤ (7027539386229/20000000000000 : ℝ)^3229 := by
    have hnat : (564999449 : ℕ)^4253*20000000000000^3229 ≤ 7027539386229^3229*1250000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      564999449 1250000000 7027539386229 20000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4253/1024 : ℝ)) 4253 3229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4339601187/10000000000 : ℝ), (4166095617/10000000000 : ℝ), (564999449/1250000000 : ℝ)] ![(832560347837/2500000000000 : ℝ), (15779944568831/50000000000000 : ℝ), (7027539386229/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4339601187/10000000000 : ℝ)|^4253 ≤ (832560347837/2500000000000 : ℝ)^3229
        have hw : |(4339601187/10000000000 : ℝ)|=(4339601187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4166095617/10000000000 : ℝ)|^4253 ≤ (15779944568831/50000000000000 : ℝ)^3229
        have hw : |(4166095617/10000000000 : ℝ)|=(4166095617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(564999449/1250000000 : ℝ)|^4253 ≤ (7027539386229/20000000000000 : ℝ)^3229
        have hw : |(564999449/1250000000 : ℝ)|=(564999449/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1293_s7_4 (p : ℝ) (hpa : (1063/256 : ℝ) ≤ p) (hpb : p ≤ (4253/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1043544809/5000000000 : ℝ)*x 0 + (5243651393/10000000000 : ℝ)*x 1 + (5414549931/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1043544809/5000000000 : ℝ)^4253 ≤ (793651560423/6250000000000 : ℝ)^3229 := by
    have hnat : (1043544809 : ℕ)^4253*6250000000000^3229 ≤ 793651560423^3229*5000000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043544809 5000000000 793651560423 6250000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5243651393/10000000000 : ℝ)^4253 ≤ (8545793343083/20000000000000 : ℝ)^3229 := by
    have hnat : (5243651393 : ℕ)^4253*20000000000000^3229 ≤ 8545793343083^3229*10000000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243651393 10000000000 8545793343083 20000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5414549931/10000000000 : ℝ)^4253 ≤ (44572608297011/100000000000000 : ℝ)^3229 := by
    have hnat : (5414549931 : ℕ)^4253*100000000000000^3229 ≤ 44572608297011^3229*10000000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5414549931 10000000000 44572608297011 100000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4253/1024 : ℝ)) 4253 3229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1043544809/5000000000 : ℝ), (5243651393/10000000000 : ℝ), (5414549931/10000000000 : ℝ)] ![(793651560423/6250000000000 : ℝ), (8545793343083/20000000000000 : ℝ), (44572608297011/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1043544809/5000000000 : ℝ)|^4253 ≤ (793651560423/6250000000000 : ℝ)^3229
        have hw : |(-1043544809/5000000000 : ℝ)|=(1043544809/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5243651393/10000000000 : ℝ)|^4253 ≤ (8545793343083/20000000000000 : ℝ)^3229
        have hw : |(5243651393/10000000000 : ℝ)|=(5243651393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5414549931/10000000000 : ℝ)|^4253 ≤ (44572608297011/100000000000000 : ℝ)^3229
        have hw : |(5414549931/10000000000 : ℝ)|=(5414549931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1293_s7_5 (p : ℝ) (hpa : (1063/256 : ℝ) ≤ p) (hpb : p ≤ (4253/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2652845541/5000000000 : ℝ)*x 0 + (-500826439/2500000000 : ℝ)*x 1 + (2707274967/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652845541/5000000000 : ℝ)^4253 ≤ (43396076533237/100000000000000 : ℝ)^3229 := by
    have hnat : (2652845541 : ℕ)^4253*100000000000000^3229 ≤ 43396076533237^3229*5000000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652845541 5000000000 43396076533237 100000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (500826439/2500000000 : ℝ)^4253 ≤ (2406263025841/20000000000000 : ℝ)^3229 := by
    have hnat : (500826439 : ℕ)^4253*20000000000000^3229 ≤ 2406263025841^3229*2500000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      500826439 2500000000 2406263025841 20000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2707274967/5000000000 : ℝ)^4253 ≤ (22286304164769/50000000000000 : ℝ)^3229 := by
    have hnat : (2707274967 : ℕ)^4253*50000000000000^3229 ≤ 22286304164769^3229*5000000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2707274967 5000000000 22286304164769 50000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4253/1024 : ℝ)) 4253 3229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652845541/5000000000 : ℝ), (-500826439/2500000000 : ℝ), (2707274967/5000000000 : ℝ)] ![(43396076533237/100000000000000 : ℝ), (2406263025841/20000000000000 : ℝ), (22286304164769/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652845541/5000000000 : ℝ)|^4253 ≤ (43396076533237/100000000000000 : ℝ)^3229
        have hw : |(2652845541/5000000000 : ℝ)|=(2652845541/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-500826439/2500000000 : ℝ)|^4253 ≤ (2406263025841/20000000000000 : ℝ)^3229
        have hw : |(-500826439/2500000000 : ℝ)|=(500826439/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2707274967/5000000000 : ℝ)|^4253 ≤ (22286304164769/50000000000000 : ℝ)^3229
        have hw : |(2707274967/5000000000 : ℝ)|=(2707274967/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1293_s7_6 (p : ℝ) (hpa : (1063/256 : ℝ) ≤ p) (hpb : p ≤ (4253/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1326422771/2500000000 : ℝ)*x 0 + (541454993/1000000000 : ℝ)*x 1 + (-1001652879/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1326422771/2500000000 : ℝ)^4253 ≤ (43396076554783/100000000000000 : ℝ)^3229 := by
    have hnat : (1326422771 : ℕ)^4253*100000000000000^3229 ≤ 43396076554783^3229*2500000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1326422771 2500000000 43396076554783 100000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (541454993/1000000000 : ℝ)^4253 ≤ (5571576035771/12500000000000 : ℝ)^3229 := by
    have hnat : (541454993 : ℕ)^4253*12500000000000^3229 ≤ 5571576035771^3229*1000000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      541454993 1000000000 5571576035771 12500000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1001652879/5000000000 : ℝ)^4253 ≤ (481252605801/4000000000000 : ℝ)^3229 := by
    have hnat : (1001652879 : ℕ)^4253*4000000000000^3229 ≤ 481252605801^3229*5000000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1001652879 5000000000 481252605801 4000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4253/1024 : ℝ)) 4253 3229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1326422771/2500000000 : ℝ), (541454993/1000000000 : ℝ), (-1001652879/5000000000 : ℝ)] ![(43396076554783/100000000000000 : ℝ), (5571576035771/12500000000000 : ℝ), (481252605801/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1326422771/2500000000 : ℝ)|^4253 ≤ (43396076554783/100000000000000 : ℝ)^3229
        have hw : |(1326422771/2500000000 : ℝ)|=(1326422771/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(541454993/1000000000 : ℝ)|^4253 ≤ (5571576035771/12500000000000 : ℝ)^3229
        have hw : |(541454993/1000000000 : ℝ)|=(541454993/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1001652879/5000000000 : ℝ)|^4253 ≤ (481252605801/4000000000000 : ℝ)^3229
        have hw : |(-1001652879/5000000000 : ℝ)|=(1001652879/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1293_s7_7 (p : ℝ) (hpa : (1063/256 : ℝ) ≤ p) (hpb : p ≤ (4253/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4339625591/10000000000 : ℝ)*x 0 + (2259367653/5000000000 : ℝ)*x 1 + (2083682037/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4339625591/10000000000 : ℝ)^4253 ≤ (8325665145629/25000000000000 : ℝ)^3229 := by
    have hnat : (4339625591 : ℕ)^4253*25000000000000^3229 ≤ 8325665145629^3229*10000000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4339625591 10000000000 8325665145629 25000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2259367653/5000000000 : ℝ)^4253 ≤ (17562396641257/50000000000000 : ℝ)^3229 := by
    have hnat : (2259367653 : ℕ)^4253*50000000000000^3229 ≤ 17562396641257^3229*5000000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2259367653 5000000000 17562396641257 50000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2083682037/5000000000 : ℝ)^4253 ≤ (31572546123311/100000000000000 : ℝ)^3229 := by
    have hnat : (2083682037 : ℕ)^4253*100000000000000^3229 ≤ 31572546123311^3229*5000000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2083682037 5000000000 31572546123311 100000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4253/1024 : ℝ)) 4253 3229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4339625591/10000000000 : ℝ), (2259367653/5000000000 : ℝ), (2083682037/5000000000 : ℝ)] ![(8325665145629/25000000000000 : ℝ), (17562396641257/50000000000000 : ℝ), (31572546123311/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4339625591/10000000000 : ℝ)|^4253 ≤ (8325665145629/25000000000000 : ℝ)^3229
        have hw : |(4339625591/10000000000 : ℝ)|=(4339625591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2259367653/5000000000 : ℝ)|^4253 ≤ (17562396641257/50000000000000 : ℝ)^3229
        have hw : |(2259367653/5000000000 : ℝ)|=(2259367653/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2083682037/5000000000 : ℝ)|^4253 ≤ (31572546123311/100000000000000 : ℝ)^3229
        have hw : |(2083682037/5000000000 : ℝ)|=(2083682037/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1293_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1063/256 : ℝ) ≤ p) (hpb : p ≤ (4253/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76400563/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (587/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2757/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (1103/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14673/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (587/4000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2757/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (587/4000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2757/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (587/4000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2757/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (587/4000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2757/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (587/4000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2757/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (587/4000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2757/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2757/25000 : ℝ) ^ (1063/256 : ℝ) ≤ (1321379023202857/12500000000000000000 : ℝ) := by
    have hpowers : (2757/25000 : ℝ)^1063 ≤ (1321379023202857/12500000000000000000 : ℝ)^256 := by
      have hnat : (2757 : ℕ)^1063*12500000000000000000^256 ≤ 1321379023202857^256*25000^1063 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2757 25000 1321379023202857 12500000000000000000 1063 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2757/25000 : ℝ)) (X := (1321379023202857/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 1063 256 (by norm_num) hpowers
    exact h
  have hpowhi : (587/4000 : ℝ) ^ (1063/256 : ℝ) ≤ (34621495500767389/100000000000000000000 : ℝ) := by
    have hpowers : (587/4000 : ℝ)^1063 ≤ (34621495500767389/100000000000000000000 : ℝ)^256 := by
      have hnat : (587 : ℕ)^1063*100000000000000000000^256 ≤ 34621495500767389^256*4000^1063 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        587 4000 34621495500767389 100000000000000000000 1063 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (587/4000 : ℝ)) (X := (34621495500767389/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1063 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (6251321379023202857/6250000000000000000 : ℝ) ≤ (2000101823785093/2000000000000000 : ℝ) ^ (1063/256 : ℝ) := by
    have hpowers : (6251321379023202857/6250000000000000000 : ℝ)^256 ≤ (2000101823785093/2000000000000000 : ℝ)^1063 := by
      have hnat : (6251321379023202857 : ℕ)^256*2000000000000000^1063 ≤ 2000101823785093^1063*6250000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6251321379023202857 6250000000000000000 2000101823785093 2000000000000000 256 1063 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000101823785093/2000000000000000 : ℝ)) (X := (6251321379023202857/6250000000000000000 : ℝ)) (by norm_num) 1063 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (20009038505537278049/20000000000000000000 : ℝ) ≤ (200021763505109/200000000000000 : ℝ) ^ (1063/256 : ℝ) := by
    have hpowers : (20009038505537278049/20000000000000000000 : ℝ)^256 ≤ (200021763505109/200000000000000 : ℝ)^1063 := by
      have hnat : (20009038505537278049 : ℕ)^256*200000000000000^1063 ≤ 200021763505109^1063*20000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20009038505537278049 20000000000000000000 200021763505109 200000000000000 256 1063 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (200021763505109/200000000000000 : ℝ)) (X := (20009038505537278049/20000000000000000000 : ℝ)) (by norm_num) 1063 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (50034621495500767389/50000000000000000000 : ℝ) ≤ (2000333446317087/2000000000000000 : ℝ) ^ (1063/256 : ℝ) := by
    have hpowers : (50034621495500767389/50000000000000000000 : ℝ)^256 ≤ (2000333446317087/2000000000000000 : ℝ)^1063 := by
      have hnat : (50034621495500767389 : ℕ)^256*2000000000000000^1063 ≤ 2000333446317087^1063*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50034621495500767389 50000000000000000000 2000333446317087 2000000000000000 256 1063 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000333446317087/2000000000000000 : ℝ)) (X := (50034621495500767389/50000000000000000000 : ℝ)) (by norm_num) 1063 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1321379023202857/12500000000000000000 : ℝ) ≤ ((1041688145437343477/1042000000000000000 : ℝ)+2*(16544466571/10420000000000 : ℝ)*(2757/25000 : ℝ))^(1063/256 : ℝ) := by
    rw [show (1041688145437343477/1042000000000000000 : ℝ)+2*(16544466571/10420000000000 : ℝ)*(2757/25000 : ℝ)=(2000101823785093/2000000000000000 : ℝ) by norm_num, show 1+2*(1321379023202857/12500000000000000000 : ℝ)=(6251321379023202857/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(34621495500767389/100000000000000000000 : ℝ)+(1321379023202857/12500000000000000000 : ℝ) ≤ ((1041688145437343477/1042000000000000000 : ℝ)+(16544466571/10420000000000 : ℝ)*((587/4000 : ℝ)+(2757/25000 : ℝ)))^(1063/256 : ℝ) := by
    rw [show (1041688145437343477/1042000000000000000 : ℝ)+(16544466571/10420000000000 : ℝ)*((587/4000 : ℝ)+(2757/25000 : ℝ))=(200021763505109/200000000000000 : ℝ) by norm_num, show 1+(34621495500767389/100000000000000000000 : ℝ)+(1321379023202857/12500000000000000000 : ℝ)=(20009038505537278049/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(34621495500767389/100000000000000000000 : ℝ) ≤ ((1041688145437343477/1042000000000000000 : ℝ)+2*(16544466571/10420000000000 : ℝ)*(587/4000 : ℝ))^(1063/256 : ℝ) := by
    rw [show (1041688145437343477/1042000000000000000 : ℝ)+2*(16544466571/10420000000000 : ℝ)*(587/4000 : ℝ)=(2000333446317087/2000000000000000 : ℝ) by norm_num, show 1+2*(34621495500767389/100000000000000000000 : ℝ)=(50034621495500767389/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1041688145437343477/1042000000000000000 : ℝ)*(X 1 0+X 2 0)+(16544466571/10420000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1063/256 : ℝ)) (lo := (2757/25000 : ℝ)) (hi := (587/4000 : ℝ)) (c := (1041688145437343477/1042000000000000000 : ℝ)) (alpha := (16544466571/10420000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1041688145437343477/1042000000000000000 : ℝ)*(X 0 1+X 2 1)+(16544466571/10420000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1063/256 : ℝ)) (lo := (2757/25000 : ℝ)) (hi := (587/4000 : ℝ)) (c := (1041688145437343477/1042000000000000000 : ℝ)) (alpha := (16544466571/10420000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1041688145437343477/1042000000000000000 : ℝ)*(X 0 2+X 1 2)+(16544466571/10420000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1063/256 : ℝ)) (lo := (2757/25000 : ℝ)) (hi := (587/4000 : ℝ)) (c := (1041688145437343477/1042000000000000000 : ℝ)) (alpha := (16544466571/10420000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-130442341/625000000 : ℝ)*X 0 0+(5415166757/10000000000 : ℝ)*X 0 1+(131075933/250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1293_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((267488303/500000000 : ℝ)*X 1 0+(-1087409473/5000000000 : ℝ)*X 1 1+(5243036961/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1293_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2674882821/5000000000 : ℝ)*X 2 0+(5243039241/10000000000 : ℝ)*X 2 1+(-2174816487/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1293_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4339601187/10000000000 : ℝ)*X 0 0+(4166095617/10000000000 : ℝ)*X 0 1+(564999449/1250000000 : ℝ)*X 0 2+(4339601187/10000000000 : ℝ)*X 1 0+(4166095617/10000000000 : ℝ)*X 1 1+(564999449/1250000000 : ℝ)*X 1 2+(4339601187/10000000000 : ℝ)*X 2 0+(4166095617/10000000000 : ℝ)*X 2 1+(564999449/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1293_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1043544809/5000000000 : ℝ)*X 0 0+(5243651393/10000000000 : ℝ)*X 0 1+(5414549931/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1293_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2652845541/5000000000 : ℝ)*X 1 0+(-500826439/2500000000 : ℝ)*X 1 1+(2707274967/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1293_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1326422771/2500000000 : ℝ)*X 2 0+(541454993/1000000000 : ℝ)*X 2 1+(-1001652879/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1293_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4339625591/10000000000 : ℝ)*X 0 0+(2259367653/5000000000 : ℝ)*X 0 1+(2083682037/5000000000 : ℝ)*X 0 2+(4339625591/10000000000 : ℝ)*X 1 0+(2259367653/5000000000 : ℝ)*X 1 1+(2083682037/5000000000 : ℝ)*X 1 2+(4339625591/10000000000 : ℝ)*X 2 0+(2259367653/5000000000 : ℝ)*X 2 1+(2083682037/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1293_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (584740004143001480397/130250000000000000000000000 : ℝ) := by norm_num
    linear_combination (2506563867/100000000000000 : ℝ)*(base19) + (206075283/10000000000000 : ℝ)*(base23) + (51004577/25000000000000 : ℝ)*(lower2) + (990370851/100000000000000 : ℝ)*(upper5) + (2158868311636809/50000000000000 : ℝ)*(major0) + (2158868311636809/50000000000000 : ℝ)*(major1) + (2158868311636809/50000000000000 : ℝ)*(major2) + (5809645421008489/100000000000000 : ℝ)*(sp0) + (5809700274358173/100000000000000 : ℝ)*(sp1) + (2904873997906823/50000000000000 : ℝ)*(sp2) + (1412848321104391/50000000000000 : ℝ)*(sp3) + (104635557987/100000000000000 : ℝ)*(sp4) + (11818911109/25000000000000 : ℝ)*(sp5) + (13199063209/50000000000000 : ℝ)*(sp7) + (2825723040335199/100000000000000 : ℝ)*(f.failure) + (1452437514141619/25000000000000 : ℝ)*(f.sum) + (923843601971/130250000000000000000000000 : ℝ)*base66 + (333935722724544893/52100000000000000000000000000000 : ℝ)*base67 + (166953978778155107/52100000000000000000000000000000 : ℝ)*base70 + (115701184745255107/52100000000000000000000000000000 : ℝ)*base72 + (9251290581/52100000000000000000000000 : ℝ)*base74 + (1196943729911844893/52100000000000000000000000000000 : ℝ)*base75 + (173971002205255107/52100000000000000000000000000000 : ℝ)*base78 + (84436292718344893/52100000000000000000000000000000 : ℝ)*base79 + (737980753219/130250000000000000000000000 : ℝ)*base82 + (12317037/5000000000000000000000 : ℝ)*base89 + (12317037/5000000000000000000000 : ℝ)*base91 + (12317037/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (72444955685912971810072233/13025000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (963078417/100000000000000 : ℝ)*(base19) + (527894911/50000000000000 : ℝ)*(base23) + (333075291/100000000000000 : ℝ)*(lower1) + (11029493/10000000000000 : ℝ)*(upper3) + (4164083/10000000000000 : ℝ)*(lower4) + (28551899/25000000000000 : ℝ)*(upper5) + (1087173520667581/25000000000000 : ℝ)*(major0) + (1087173520667581/25000000000000 : ℝ)*(major1) + (1087173520667581/25000000000000 : ℝ)*(major2) + (361812723/25000000000000 : ℝ)*(sp2) + (2925702485748697/50000000000000 : ℝ)*(sp4) + (5851404008418977/100000000000000 : ℝ)*(sp5) + (146285061711417/2500000000000 : ℝ)*(sp6) + (88936969013859/3125000000000 : ℝ)*(sp7) + (88936969013859/3125000000000 : ℝ)*(f.failure) + (2925702485748697/50000000000000 : ℝ)*(f.sum) + (4939161003/2035156250000000000000000 : ℝ)*base65 + (428650174567680863/26050000000000000000000000000000 : ℝ)*base68 + (207055139861480863/26050000000000000000000000000000 : ℝ)*base70 + (658020616087280863/26050000000000000000000000000000 : ℝ)*base72 + (74899611129/65125000000000000000000000 : ℝ)*base74 + (95308916050680863/26050000000000000000000000000000 : ℝ)*base76 + (45929775040780863/26050000000000000000000000000000 : ℝ)*base78 + (87038694124180863/26050000000000000000000000000000 : ℝ)*base80 + (69818307207/16281250000000000000000000 : ℝ)*base82 + (1152617/156250000000000000000 : ℝ)*base89 + (1152617/156250000000000000000 : ℝ)*base91 + (1152617/156250000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1293_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1063/256 : ℝ) ≤ p) (hpb : p ≤ (4253/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76400563/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (587/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2757/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1103/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14673/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1293_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1293_s8_0 (p : ℝ) (hpa : (1063/256 : ℝ) ≤ p) (hpb : p ≤ (4253/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2087078037/10000000000 : ℝ)*x 0 + (2707574669/5000000000 : ℝ)*x 1 + (1310763621/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2087078037/10000000000 : ℝ)^4253 ≤ (2539666431909/20000000000000 : ℝ)^3229 := by
    have hnat : (2087078037 : ℕ)^4253*20000000000000^3229 ≤ 2539666431909^3229*10000000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2087078037 10000000000 2539666431909 20000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2707574669/5000000000 : ℝ)^4253 ≤ (44579107535251/100000000000000 : ℝ)^3229 := by
    have hnat : (2707574669 : ℕ)^4253*100000000000000^3229 ≤ 44579107535251^3229*5000000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2707574669 5000000000 44579107535251 100000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1310763621/2500000000 : ℝ)^4253 ≤ (42722560283649/100000000000000 : ℝ)^3229 := by
    have hnat : (1310763621 : ℕ)^4253*100000000000000^3229 ≤ 42722560283649^3229*2500000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310763621 2500000000 42722560283649 100000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4253/1024 : ℝ)) 4253 3229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2087078037/10000000000 : ℝ), (2707574669/5000000000 : ℝ), (1310763621/2500000000 : ℝ)] ![(2539666431909/20000000000000 : ℝ), (44579107535251/100000000000000 : ℝ), (42722560283649/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2087078037/10000000000 : ℝ)|^4253 ≤ (2539666431909/20000000000000 : ℝ)^3229
        have hw : |(-2087078037/10000000000 : ℝ)|=(2087078037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2707574669/5000000000 : ℝ)|^4253 ≤ (44579107535251/100000000000000 : ℝ)^3229
        have hw : |(2707574669/5000000000 : ℝ)|=(2707574669/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1310763621/2500000000 : ℝ)|^4253 ≤ (42722560283649/100000000000000 : ℝ)^3229
        have hw : |(1310763621/2500000000 : ℝ)|=(1310763621/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1293_s8_1 (p : ℝ) (hpa : (1063/256 : ℝ) ≤ p) (hpb : p ≤ (4253/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349761929/10000000000 : ℝ)*x 0 + (-135925079/625000000 : ℝ)*x 1 + (2621527247/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349761929/10000000000 : ℝ)^4253 ≤ (8774295002523/20000000000000 : ℝ)^3229 := by
    have hnat : (5349761929 : ℕ)^4253*20000000000000^3229 ≤ 8774295002523^3229*10000000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349761929 10000000000 8774295002523 20000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (135925079/625000000 : ℝ)^4253 ≤ (335149114401/2500000000000 : ℝ)^3229 := by
    have hnat : (135925079 : ℕ)^4253*2500000000000^3229 ≤ 335149114401^3229*625000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135925079 625000000 335149114401 2500000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2621527247/5000000000 : ℝ)^4253 ≤ (21361280195487/50000000000000 : ℝ)^3229 := by
    have hnat : (2621527247 : ℕ)^4253*50000000000000^3229 ≤ 21361280195487^3229*5000000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621527247 5000000000 21361280195487 50000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4253/1024 : ℝ)) 4253 3229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349761929/10000000000 : ℝ), (-135925079/625000000 : ℝ), (2621527247/5000000000 : ℝ)] ![(8774295002523/20000000000000 : ℝ), (335149114401/2500000000000 : ℝ), (21361280195487/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349761929/10000000000 : ℝ)|^4253 ≤ (8774295002523/20000000000000 : ℝ)^3229
        have hw : |(5349761929/10000000000 : ℝ)|=(5349761929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-135925079/625000000 : ℝ)|^4253 ≤ (335149114401/2500000000000 : ℝ)^3229
        have hw : |(-135925079/625000000 : ℝ)|=(135925079/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2621527247/5000000000 : ℝ)|^4253 ≤ (21361280195487/50000000000000 : ℝ)^3229
        have hw : |(2621527247/5000000000 : ℝ)|=(2621527247/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1293_s8_2 (p : ℝ) (hpa : (1063/256 : ℝ) ≤ p) (hpb : p ≤ (4253/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349761081/10000000000 : ℝ)*x 0 + (2621527783/5000000000 : ℝ)*x 1 + (-135925061/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349761081/10000000000 : ℝ)^4253 ≤ (10967866463283/25000000000000 : ℝ)^3229 := by
    have hnat : (5349761081 : ℕ)^4253*25000000000000^3229 ≤ 10967866463283^3229*10000000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349761081 10000000000 10967866463283 25000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2621527783/5000000000 : ℝ)^4253 ≤ (42722571896197/100000000000000 : ℝ)^3229 := by
    have hnat : (2621527783 : ℕ)^4253*100000000000000^3229 ≤ 42722571896197^3229*5000000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621527783 5000000000 42722571896197 100000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (135925061/625000000 : ℝ)^4253 ≤ (13405962237751/100000000000000 : ℝ)^3229 := by
    have hnat : (135925061 : ℕ)^4253*100000000000000^3229 ≤ 13405962237751^3229*625000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135925061 625000000 13405962237751 100000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4253/1024 : ℝ)) 4253 3229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349761081/10000000000 : ℝ), (2621527783/5000000000 : ℝ), (-135925061/625000000 : ℝ)] ![(10967866463283/25000000000000 : ℝ), (42722571896197/100000000000000 : ℝ), (13405962237751/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349761081/10000000000 : ℝ)|^4253 ≤ (10967866463283/25000000000000 : ℝ)^3229
        have hw : |(5349761081/10000000000 : ℝ)|=(5349761081/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2621527783/5000000000 : ℝ)|^4253 ≤ (42722571896197/100000000000000 : ℝ)^3229
        have hw : |(2621527783/5000000000 : ℝ)|=(2621527783/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-135925061/625000000 : ℝ)|^4253 ≤ (13405962237751/100000000000000 : ℝ)^3229
        have hw : |(-135925061/625000000 : ℝ)|=(135925061/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1293_s8_3 (p : ℝ) (hpa : (1063/256 : ℝ) ≤ p) (hpb : p ≤ (4253/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4339600043/10000000000 : ℝ)*x 0 + (2083065673/5000000000 : ℝ)*x 1 + (282497619/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4339600043/10000000000 : ℝ)^4253 ≤ (4162800293781/12500000000000 : ℝ)^3229 := by
    have hnat : (4339600043 : ℕ)^4253*12500000000000^3229 ≤ 4162800293781^3229*10000000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4339600043 10000000000 4162800293781 12500000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2083065673/5000000000 : ℝ)^4253 ≤ (789006140849/2500000000000 : ℝ)^3229 := by
    have hnat : (2083065673 : ℕ)^4253*2500000000000^3229 ≤ 789006140849^3229*5000000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2083065673 5000000000 789006140849 2500000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (282497619/625000000 : ℝ)^4253 ≤ (35137351996089/100000000000000 : ℝ)^3229 := by
    have hnat : (282497619 : ℕ)^4253*100000000000000^3229 ≤ 35137351996089^3229*625000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      282497619 625000000 35137351996089 100000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4253/1024 : ℝ)) 4253 3229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4339600043/10000000000 : ℝ), (2083065673/5000000000 : ℝ), (282497619/625000000 : ℝ)] ![(4162800293781/12500000000000 : ℝ), (789006140849/2500000000000 : ℝ), (35137351996089/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4339600043/10000000000 : ℝ)|^4253 ≤ (4162800293781/12500000000000 : ℝ)^3229
        have hw : |(4339600043/10000000000 : ℝ)|=(4339600043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2083065673/5000000000 : ℝ)|^4253 ≤ (789006140849/2500000000000 : ℝ)^3229
        have hw : |(2083065673/5000000000 : ℝ)|=(2083065673/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(282497619/625000000 : ℝ)|^4253 ≤ (35137351996089/100000000000000 : ℝ)^3229
        have hw : |(282497619/625000000 : ℝ)|=(282497619/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1293_s8_4 (p : ℝ) (hpa : (1063/256 : ℝ) ≤ p) (hpb : p ≤ (4253/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2087090877/10000000000 : ℝ)*x 0 + (5243668443/10000000000 : ℝ)*x 1 + (1353633031/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2087090877/10000000000 : ℝ)^4253 ≤ (12698435056087/100000000000000 : ℝ)^3229 := by
    have hnat : (2087090877 : ℕ)^4253*100000000000000^3229 ≤ 12698435056087^3229*10000000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2087090877 10000000000 12698435056087 100000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5243668443/10000000000 : ℝ)^4253 ≤ (42729149710963/100000000000000 : ℝ)^3229 := by
    have hnat : (5243668443 : ℕ)^4253*100000000000000^3229 ≤ 42729149710963^3229*10000000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243668443 10000000000 42729149710963 100000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1353633031/2500000000 : ℝ)^4253 ≤ (44572415223117/100000000000000 : ℝ)^3229 := by
    have hnat : (1353633031 : ℕ)^4253*100000000000000^3229 ≤ 44572415223117^3229*2500000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1353633031 2500000000 44572415223117 100000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4253/1024 : ℝ)) 4253 3229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2087090877/10000000000 : ℝ), (5243668443/10000000000 : ℝ), (1353633031/2500000000 : ℝ)] ![(12698435056087/100000000000000 : ℝ), (42729149710963/100000000000000 : ℝ), (44572415223117/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2087090877/10000000000 : ℝ)|^4253 ≤ (12698435056087/100000000000000 : ℝ)^3229
        have hw : |(-2087090877/10000000000 : ℝ)|=(2087090877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5243668443/10000000000 : ℝ)|^4253 ≤ (42729149710963/100000000000000 : ℝ)^3229
        have hw : |(5243668443/10000000000 : ℝ)|=(5243668443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1353633031/2500000000 : ℝ)|^4253 ≤ (44572415223117/100000000000000 : ℝ)^3229
        have hw : |(1353633031/2500000000 : ℝ)|=(1353633031/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1293_s8_5 (p : ℝ) (hpa : (1063/256 : ℝ) ≤ p) (hpb : p ≤ (4253/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (132642397/250000000 : ℝ)*x 0 + (-2003323299/10000000000 : ℝ)*x 1 + (338408273/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (132642397/250000000 : ℝ)^4253 ≤ (43396128222001/100000000000000 : ℝ)^3229 := by
    have hnat : (132642397 : ℕ)^4253*100000000000000^3229 ≤ 43396128222001^3229*250000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132642397 250000000 43396128222001 100000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2003323299/10000000000 : ℝ)^4253 ≤ (12031453899869/100000000000000 : ℝ)^3229 := by
    have hnat : (2003323299 : ℕ)^4253*100000000000000^3229 ≤ 12031453899869^3229*10000000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2003323299 10000000000 12031453899869 100000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (338408273/625000000 : ℝ)^4253 ≤ (22286208934353/50000000000000 : ℝ)^3229 := by
    have hnat : (338408273 : ℕ)^4253*50000000000000^3229 ≤ 22286208934353^3229*625000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      338408273 625000000 22286208934353 50000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4253/1024 : ℝ)) 4253 3229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(132642397/250000000 : ℝ), (-2003323299/10000000000 : ℝ), (338408273/625000000 : ℝ)] ![(43396128222001/100000000000000 : ℝ), (12031453899869/100000000000000 : ℝ), (22286208934353/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(132642397/250000000 : ℝ)|^4253 ≤ (43396128222001/100000000000000 : ℝ)^3229
        have hw : |(132642397/250000000 : ℝ)|=(132642397/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2003323299/10000000000 : ℝ)|^4253 ≤ (12031453899869/100000000000000 : ℝ)^3229
        have hw : |(-2003323299/10000000000 : ℝ)|=(2003323299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(338408273/625000000 : ℝ)|^4253 ≤ (22286208934353/50000000000000 : ℝ)^3229
        have hw : |(338408273/625000000 : ℝ)|=(338408273/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1293_s8_6 (p : ℝ) (hpa : (1063/256 : ℝ) ≤ p) (hpb : p ≤ (4253/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2169813231/5000000000 : ℝ)*x 0 + (2259350221/5000000000 : ℝ)*x 1 + (4167398963/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2169813231/5000000000 : ℝ)^4253 ≤ (33302669386357/100000000000000 : ℝ)^3229 := by
    have hnat : (2169813231 : ℕ)^4253*100000000000000^3229 ≤ 33302669386357^3229*5000000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2169813231 5000000000 33302669386357 100000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2259350221/5000000000 : ℝ)^4253 ≤ (702488726757/2000000000000 : ℝ)^3229 := by
    have hnat : (2259350221 : ℕ)^4253*2000000000000^3229 ≤ 702488726757^3229*5000000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2259350221 5000000000 702488726757 2000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4167398963/10000000000 : ℝ)^4253 ≤ (31572894271867/100000000000000 : ℝ)^3229 := by
    have hnat : (4167398963 : ℕ)^4253*100000000000000^3229 ≤ 31572894271867^3229*10000000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4167398963 10000000000 31572894271867 100000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4253/1024 : ℝ)) 4253 3229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2169813231/5000000000 : ℝ), (2259350221/5000000000 : ℝ), (4167398963/10000000000 : ℝ)] ![(33302669386357/100000000000000 : ℝ), (702488726757/2000000000000 : ℝ), (31572894271867/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2169813231/5000000000 : ℝ)|^4253 ≤ (33302669386357/100000000000000 : ℝ)^3229
        have hw : |(2169813231/5000000000 : ℝ)|=(2169813231/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2259350221/5000000000 : ℝ)|^4253 ≤ (702488726757/2000000000000 : ℝ)^3229
        have hw : |(2259350221/5000000000 : ℝ)|=(2259350221/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4167398963/10000000000 : ℝ)|^4253 ≤ (31572894271867/100000000000000 : ℝ)^3229
        have hw : |(4167398963/10000000000 : ℝ)|=(4167398963/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1293_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1063/256 : ℝ) ≤ p) (hpb : p ≤ (4253/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76400563/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14673/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1103/10000 : ℝ)*pair X i i ≤ pair X i h) :
    (11031/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14673/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14673/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1103/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14673/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1103/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14673/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1103/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14673/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1103/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14673/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1103/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14673/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1103/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
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
  have hpowlo : (1103/10000 : ℝ) ^ (1063/256 : ℝ) ≤ (132237437839599/1250000000000000000 : ℝ) := by
    have hpowers : (1103/10000 : ℝ)^1063 ≤ (132237437839599/1250000000000000000 : ℝ)^256 := by
      have hnat : (1103 : ℕ)^1063*1250000000000000000^256 ≤ 132237437839599^256*10000^1063 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1103 10000 132237437839599 1250000000000000000 1063 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1103/10000 : ℝ)) (X := (132237437839599/1250000000000000000 : ℝ)) (by norm_num) (by norm_num) 1063 256 (by norm_num) hpowers
    exact h
  have hpowhi : (14673/100000 : ℝ) ^ (1063/256 : ℝ) ≤ (8650476789254941/25000000000000000000 : ℝ) := by
    have hpowers : (14673/100000 : ℝ)^1063 ≤ (8650476789254941/25000000000000000000 : ℝ)^256 := by
      have hnat : (14673 : ℕ)^1063*25000000000000000000^256 ≤ 8650476789254941^256*100000^1063 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14673 100000 8650476789254941 25000000000000000000 1063 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14673/100000 : ℝ)) (X := (8650476789254941/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1063 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (625132237437839599/625000000000000000 : ℝ) ≤ (10000509502398689/10000000000000000 : ℝ) ^ (1063/256 : ℝ) := by
    have hpowers : (625132237437839599/625000000000000000 : ℝ)^256 ≤ (10000509502398689/10000000000000000 : ℝ)^1063 := by
      have hnat : (625132237437839599 : ℕ)^256*10000000000000000^1063 ≤ 10000509502398689^1063*625000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        625132237437839599 625000000000000000 10000509502398689 10000000000000000 256 1063 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000509502398689/10000000000000000 : ℝ)) (X := (625132237437839599/625000000000000000 : ℝ)) (by norm_num) 1063 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (25011295225546046921/25000000000000000000 : ℝ) ≤ (1000108789537699/1000000000000000 : ℝ) ^ (1063/256 : ℝ) := by
    have hpowers : (25011295225546046921/25000000000000000000 : ℝ)^256 ≤ (1000108789537699/1000000000000000 : ℝ)^1063 := by
      have hnat : (25011295225546046921 : ℕ)^256*1000000000000000^1063 ≤ 1000108789537699^1063*25000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25011295225546046921 25000000000000000000 1000108789537699 1000000000000000 256 1063 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000108789537699/1000000000000000 : ℝ)) (X := (25011295225546046921/25000000000000000000 : ℝ)) (by norm_num) 1063 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (12508650476789254941/12500000000000000000 : ℝ) ≤ (10001666288355291/10000000000000000 : ℝ) ^ (1063/256 : ℝ) := by
    have hpowers : (12508650476789254941/12500000000000000000 : ℝ)^256 ≤ (10001666288355291/10000000000000000 : ℝ)^1063 := by
      have hnat : (12508650476789254941 : ℕ)^256*10000000000000000^1063 ≤ 10001666288355291^1063*12500000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12508650476789254941 12500000000000000000 10001666288355291 10000000000000000 256 1063 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001666288355291/10000000000000000 : ℝ)) (X := (12508650476789254941/12500000000000000000 : ℝ)) (by norm_num) 1063 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(132237437839599/1250000000000000000 : ℝ) ≤ ((36419096768137103967/36430000000000000000 : ℝ)+2*(578392978301/364300000000000 : ℝ)*(1103/10000 : ℝ))^(1063/256 : ℝ) := by
    rw [show (36419096768137103967/36430000000000000000 : ℝ)+2*(578392978301/364300000000000 : ℝ)*(1103/10000 : ℝ)=(10000509502398689/10000000000000000 : ℝ) by norm_num, show 1+2*(132237437839599/1250000000000000000 : ℝ)=(625132237437839599/625000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(8650476789254941/25000000000000000000 : ℝ)+(132237437839599/1250000000000000000 : ℝ) ≤ ((36419096768137103967/36430000000000000000 : ℝ)+(578392978301/364300000000000 : ℝ)*((14673/100000 : ℝ)+(1103/10000 : ℝ)))^(1063/256 : ℝ) := by
    rw [show (36419096768137103967/36430000000000000000 : ℝ)+(578392978301/364300000000000 : ℝ)*((14673/100000 : ℝ)+(1103/10000 : ℝ))=(1000108789537699/1000000000000000 : ℝ) by norm_num, show 1+(8650476789254941/25000000000000000000 : ℝ)+(132237437839599/1250000000000000000 : ℝ)=(25011295225546046921/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(8650476789254941/25000000000000000000 : ℝ) ≤ ((36419096768137103967/36430000000000000000 : ℝ)+2*(578392978301/364300000000000 : ℝ)*(14673/100000 : ℝ))^(1063/256 : ℝ) := by
    rw [show (36419096768137103967/36430000000000000000 : ℝ)+2*(578392978301/364300000000000 : ℝ)*(14673/100000 : ℝ)=(10001666288355291/10000000000000000 : ℝ) by norm_num, show 1+2*(8650476789254941/25000000000000000000 : ℝ)=(12508650476789254941/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (36419096768137103967/36430000000000000000 : ℝ)*(X 1 0+X 2 0)+(578392978301/364300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1063/256 : ℝ)) (lo := (1103/10000 : ℝ)) (hi := (14673/100000 : ℝ)) (c := (36419096768137103967/36430000000000000000 : ℝ)) (alpha := (578392978301/364300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (36419096768137103967/36430000000000000000 : ℝ)*(X 0 1+X 2 1)+(578392978301/364300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1063/256 : ℝ)) (lo := (1103/10000 : ℝ)) (hi := (14673/100000 : ℝ)) (c := (36419096768137103967/36430000000000000000 : ℝ)) (alpha := (578392978301/364300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (36419096768137103967/36430000000000000000 : ℝ)*(X 0 2+X 1 2)+(578392978301/364300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1063/256 : ℝ)) (lo := (1103/10000 : ℝ)) (hi := (14673/100000 : ℝ)) (c := (36419096768137103967/36430000000000000000 : ℝ)) (alpha := (578392978301/364300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2087078037/10000000000 : ℝ)*X 0 0+(2707574669/5000000000 : ℝ)*X 0 1+(1310763621/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1293_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5349761929/10000000000 : ℝ)*X 1 0+(-135925079/625000000 : ℝ)*X 1 1+(2621527247/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1293_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5349761081/10000000000 : ℝ)*X 2 0+(2621527783/5000000000 : ℝ)*X 2 1+(-135925061/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1293_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4339600043/10000000000 : ℝ)*X 0 0+(2083065673/5000000000 : ℝ)*X 0 1+(282497619/625000000 : ℝ)*X 0 2+(4339600043/10000000000 : ℝ)*X 1 0+(2083065673/5000000000 : ℝ)*X 1 1+(282497619/625000000 : ℝ)*X 1 2+(4339600043/10000000000 : ℝ)*X 2 0+(2083065673/5000000000 : ℝ)*X 2 1+(282497619/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1293_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2087090877/10000000000 : ℝ)*X 0 0+(5243668443/10000000000 : ℝ)*X 0 1+(1353633031/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1293_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((132642397/250000000 : ℝ)*X 1 0+(-2003323299/10000000000 : ℝ)*X 1 1+(338408273/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1293_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2169813231/5000000000 : ℝ)*X 0 0+(2259350221/5000000000 : ℝ)*X 0 1+(4167398963/10000000000 : ℝ)*X 0 2+(2169813231/5000000000 : ℝ)*X 1 0+(2259350221/5000000000 : ℝ)*X 1 1+(4167398963/10000000000 : ℝ)*X 1 2+(2169813231/5000000000 : ℝ)*X 2 0+(2259350221/5000000000 : ℝ)*X 2 1+(4167398963/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1293_s8_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (362244845238064750046288637/182150000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (253777837/50000000000000 : ℝ)*(base21) + (3577677/20000000000000 : ℝ)*(upper2) + (230444411/50000000000000 : ℝ)*(lower3) + (10667967/5000000000000 : ℝ)*(lower4) + (431851905728337/10000000000000 : ℝ)*(major0) + (431851905728337/10000000000000 : ℝ)*(major1) + (431851905728337/10000000000000 : ℝ)*(major2) + (1452692487083323/25000000000000 : ℝ)*(sp0) + (1452699291173933/25000000000000 : ℝ)*(sp1) + (5810802440016207/100000000000000 : ℝ)*(sp2) + (2826227273033917/100000000000000 : ℝ)*(sp3) + (32999238589/100000000000000 : ℝ)*(sp4) + (1445719037/25000000000000 : ℝ)*(sp5) + (7827670361/100000000000000 : ℝ)*(sp6) + (1413117550352139/50000000000000 : ℝ)*(f.failure) + (145270073689297/2500000000000 : ℝ)*(f.sum) + (14781820971233/1821500000000000000000000000 : ℝ)*base65 + (2005387524257387121/364300000000000000000000000000000 : ℝ)*base68 + (541259455278212879/364300000000000000000000000000000 : ℝ)*base69 + (1336146207057587121/364300000000000000000000000000000 : ℝ)*base72 + (679597682841/1821500000000000000000000000 : ℝ)*base73 + (1758617556453812879/364300000000000000000000000000000 : ℝ)*base75 + (4360412711443287121/364300000000000000000000000000000 : ℝ)*base78 + (2987995895615087121/364300000000000000000000000000000 : ℝ)*base80 + (7641314223423/3643000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (17854257/2500000000000000000000 : ℝ)*base89 + (17854257/2500000000000000000000 : ℝ)*base91 + (17854257/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(upper0) + hcertificate_margin
theorem rectangle_w1293_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1063/256 : ℝ) ≤ p) (hpb : p ≤ (4253/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76400563/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14673/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1103/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11031/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14673/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1293_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1293_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1063/256 : ℝ) ≤ p) (hpb : p ≤ (4253/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76400563/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14687/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11017/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11031/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14673/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1293_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1293_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1293_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (1063/256 : ℝ) ≤ p) (hpb : p ≤ (4253/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76400563/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14687/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11017/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11031/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14673/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1293_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
