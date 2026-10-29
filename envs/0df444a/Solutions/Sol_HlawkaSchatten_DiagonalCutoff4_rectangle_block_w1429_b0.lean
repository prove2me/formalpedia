-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1429_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:53:39.838601+00:00
-- url     : https://prove2.me/submissions/47155f74-4829-42f6-8273-45633887142a

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
theorem support_rectangle_w1429_s0_0 (p : ℝ) (hpa : (1097/256 : ℝ) ≤ p) (hpb : p ≤ (4389/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-219851731/1250000000 : ℝ)*x 0 + (149004523/250000000 : ℝ)*x 1 + (2415619057/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (219851731/1250000000 : ℝ)^4389 ≤ (10364144120279/100000000000000 : ℝ)^3365 := by
    have hnat : (219851731 : ℕ)^4389*100000000000000^3365 ≤ 10364144120279^3365*1250000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      219851731 1250000000 10364144120279 100000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (149004523/250000000 : ℝ)^4389 ≤ (50917708951899/100000000000000 : ℝ)^3365 := by
    have hnat : (149004523 : ℕ)^4389*100000000000000^3365 ≤ 50917708951899^3365*250000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      149004523 250000000 50917708951899 100000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2415619057/5000000000 : ℝ)^4389 ≤ (19359073451471/50000000000000 : ℝ)^3365 := by
    have hnat : (2415619057 : ℕ)^4389*50000000000000^3365 ≤ 19359073451471^3365*5000000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2415619057 5000000000 19359073451471 50000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4389/1024 : ℝ)) 4389 3365 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-219851731/1250000000 : ℝ), (149004523/250000000 : ℝ), (2415619057/5000000000 : ℝ)] ![(10364144120279/100000000000000 : ℝ), (50917708951899/100000000000000 : ℝ), (19359073451471/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-219851731/1250000000 : ℝ)|^4389 ≤ (10364144120279/100000000000000 : ℝ)^3365
        have hw : |(-219851731/1250000000 : ℝ)|=(219851731/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(149004523/250000000 : ℝ)|^4389 ≤ (50917708951899/100000000000000 : ℝ)^3365
        have hw : |(149004523/250000000 : ℝ)|=(149004523/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2415619057/5000000000 : ℝ)|^4389 ≤ (19359073451471/50000000000000 : ℝ)^3365
        have hw : |(2415619057/5000000000 : ℝ)|=(2415619057/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1429_s0_1 (p : ℝ) (hpa : (1097/256 : ℝ) ≤ p) (hpb : p ≤ (4389/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (43936793/80000000 : ℝ)*x 0 + (-1198274889/5000000000 : ℝ)*x 1 + (966247711/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (43936793/80000000 : ℝ)^4389 ≤ (2288275957247/5000000000000 : ℝ)^3365 := by
    have hnat : (43936793 : ℕ)^4389*5000000000000^3365 ≤ 2288275957247^3365*80000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      43936793 80000000 2288275957247 5000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1198274889/5000000000 : ℝ)^4389 ≤ (7758164661483/50000000000000 : ℝ)^3365 := by
    have hnat : (1198274889 : ℕ)^4389*50000000000000^3365 ≤ 7758164661483^3365*5000000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1198274889 5000000000 7758164661483 50000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (966247711/2000000000 : ℝ)^4389 ≤ (38718151512669/100000000000000 : ℝ)^3365 := by
    have hnat : (966247711 : ℕ)^4389*100000000000000^3365 ≤ 38718151512669^3365*2000000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      966247711 2000000000 38718151512669 100000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4389/1024 : ℝ)) 4389 3365 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(43936793/80000000 : ℝ), (-1198274889/5000000000 : ℝ), (966247711/2000000000 : ℝ)] ![(2288275957247/5000000000000 : ℝ), (7758164661483/50000000000000 : ℝ), (38718151512669/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(43936793/80000000 : ℝ)|^4389 ≤ (2288275957247/5000000000000 : ℝ)^3365
        have hw : |(43936793/80000000 : ℝ)|=(43936793/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1198274889/5000000000 : ℝ)|^4389 ≤ (7758164661483/50000000000000 : ℝ)^3365
        have hw : |(-1198274889/5000000000 : ℝ)|=(1198274889/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(966247711/2000000000 : ℝ)|^4389 ≤ (38718151512669/100000000000000 : ℝ)^3365
        have hw : |(966247711/2000000000 : ℝ)|=(966247711/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1429_s0_2 (p : ℝ) (hpa : (1097/256 : ℝ) ≤ p) (hpb : p ≤ (4389/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1098419931/2000000000 : ℝ)*x 0 + (2415619183/5000000000 : ℝ)*x 1 + (-2396549331/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1098419931/2000000000 : ℝ)^4389 ≤ (4576552490539/10000000000000 : ℝ)^3365 := by
    have hnat : (1098419931 : ℕ)^4389*10000000000000^3365 ≤ 4576552490539^3365*2000000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1098419931 2000000000 4576552490539 10000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2415619183/5000000000 : ℝ)^4389 ≤ (2419884346067/6250000000000 : ℝ)^3365 := by
    have hnat : (2415619183 : ℕ)^4389*6250000000000^3365 ≤ 2419884346067^3365*5000000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2415619183 5000000000 2419884346067 6250000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2396549331/10000000000 : ℝ)^4389 ≤ (3103265109639/20000000000000 : ℝ)^3365 := by
    have hnat : (2396549331 : ℕ)^4389*20000000000000^3365 ≤ 3103265109639^3365*10000000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2396549331 10000000000 3103265109639 20000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4389/1024 : ℝ)) 4389 3365 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1098419931/2000000000 : ℝ), (2415619183/5000000000 : ℝ), (-2396549331/10000000000 : ℝ)] ![(4576552490539/10000000000000 : ℝ), (2419884346067/6250000000000 : ℝ), (3103265109639/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1098419931/2000000000 : ℝ)|^4389 ≤ (4576552490539/10000000000000 : ℝ)^3365
        have hw : |(1098419931/2000000000 : ℝ)|=(1098419931/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2415619183/5000000000 : ℝ)|^4389 ≤ (2419884346067/6250000000000 : ℝ)^3365
        have hw : |(2415619183/5000000000 : ℝ)|=(2415619183/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2396549331/10000000000 : ℝ)|^4389 ≤ (3103265109639/20000000000000 : ℝ)^3365
        have hw : |(-2396549331/10000000000 : ℝ)|=(2396549331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1429_s0_3 (p : ℝ) (hpa : (1097/256 : ℝ) ≤ p) (hpb : p ≤ (4389/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2083000269/5000000000 : ℝ)*x 0 + (620671359/2000000000 : ℝ)*x 1 + (1109127693/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2083000269/5000000000 : ℝ)^4389 ≤ (31915118733167/100000000000000 : ℝ)^3365 := by
    have hnat : (2083000269 : ℕ)^4389*100000000000000^3365 ≤ 31915118733167^3365*5000000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2083000269 5000000000 31915118733167 100000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (620671359/2000000000 : ℝ)^4389 ≤ (2717074245021/12500000000000 : ℝ)^3365 := by
    have hnat : (620671359 : ℕ)^4389*12500000000000^3365 ≤ 2717074245021^3365*2000000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      620671359 2000000000 2717074245021 12500000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1109127693/2000000000 : ℝ)^4389 ≤ (9269657457081/20000000000000 : ℝ)^3365 := by
    have hnat : (1109127693 : ℕ)^4389*20000000000000^3365 ≤ 9269657457081^3365*2000000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1109127693 2000000000 9269657457081 20000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4389/1024 : ℝ)) 4389 3365 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2083000269/5000000000 : ℝ), (620671359/2000000000 : ℝ), (1109127693/2000000000 : ℝ)] ![(31915118733167/100000000000000 : ℝ), (2717074245021/12500000000000 : ℝ), (9269657457081/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2083000269/5000000000 : ℝ)|^4389 ≤ (31915118733167/100000000000000 : ℝ)^3365
        have hw : |(2083000269/5000000000 : ℝ)|=(2083000269/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(620671359/2000000000 : ℝ)|^4389 ≤ (2717074245021/12500000000000 : ℝ)^3365
        have hw : |(620671359/2000000000 : ℝ)|=(620671359/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1109127693/2000000000 : ℝ)|^4389 ≤ (9269657457081/20000000000000 : ℝ)^3365
        have hw : |(1109127693/2000000000 : ℝ)|=(1109127693/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1429_s0_4 (p : ℝ) (hpa : (1097/256 : ℝ) ≤ p) (hpb : p ≤ (4389/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-176283099/1000000000 : ℝ)*x 0 + (4860123187/10000000000 : ℝ)*x 1 + (593026463/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (176283099/1000000000 : ℝ)^4389 ≤ (10395030149919/100000000000000 : ℝ)^3365 := by
    have hnat : (176283099 : ℕ)^4389*100000000000000^3365 ≤ 10395030149919^3365*1000000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      176283099 1000000000 10395030149919 100000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4860123187/10000000000 : ℝ)^4389 ≤ (39020353858649/100000000000000 : ℝ)^3365 := by
    have hnat : (4860123187 : ℕ)^4389*100000000000000^3365 ≤ 39020353858649^3365*10000000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4860123187 10000000000 39020353858649 100000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (593026463/1000000000 : ℝ)^4389 ≤ (50584615982839/100000000000000 : ℝ)^3365 := by
    have hnat : (593026463 : ℕ)^4389*100000000000000^3365 ≤ 50584615982839^3365*1000000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      593026463 1000000000 50584615982839 100000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4389/1024 : ℝ)) 4389 3365 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-176283099/1000000000 : ℝ), (4860123187/10000000000 : ℝ), (593026463/1000000000 : ℝ)] ![(10395030149919/100000000000000 : ℝ), (39020353858649/100000000000000 : ℝ), (50584615982839/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-176283099/1000000000 : ℝ)|^4389 ≤ (10395030149919/100000000000000 : ℝ)^3365
        have hw : |(-176283099/1000000000 : ℝ)|=(176283099/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4860123187/10000000000 : ℝ)|^4389 ≤ (39020353858649/100000000000000 : ℝ)^3365
        have hw : |(4860123187/10000000000 : ℝ)|=(4860123187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(593026463/1000000000 : ℝ)|^4389 ≤ (50584615982839/100000000000000 : ℝ)^3365
        have hw : |(593026463/1000000000 : ℝ)|=(593026463/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1429_s0_5 (p : ℝ) (hpa : (1097/256 : ℝ) ≤ p) (hpb : p ≤ (4389/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (518396603/1000000000 : ℝ)*x 0 + (-1297523013/10000000000 : ℝ)*x 1 + (46330193/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (518396603/1000000000 : ℝ)^4389 ≤ (21222730364429/50000000000000 : ℝ)^3365 := by
    have hnat : (518396603 : ℕ)^4389*50000000000000^3365 ≤ 21222730364429^3365*1000000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      518396603 1000000000 21222730364429 50000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1297523013/10000000000 : ℝ)^4389 ≤ (174248061343/2500000000000 : ℝ)^3365 := by
    have hnat : (1297523013 : ℕ)^4389*2500000000000^3365 ≤ 174248061343^3365*10000000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1297523013 10000000000 174248061343 2500000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (46330193/78125000 : ℝ)^4389 ≤ (6323077100767/12500000000000 : ℝ)^3365 := by
    have hnat : (46330193 : ℕ)^4389*12500000000000^3365 ≤ 6323077100767^3365*78125000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      46330193 78125000 6323077100767 12500000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4389/1024 : ℝ)) 4389 3365 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(518396603/1000000000 : ℝ), (-1297523013/10000000000 : ℝ), (46330193/78125000 : ℝ)] ![(21222730364429/50000000000000 : ℝ), (174248061343/2500000000000 : ℝ), (6323077100767/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(518396603/1000000000 : ℝ)|^4389 ≤ (21222730364429/50000000000000 : ℝ)^3365
        have hw : |(518396603/1000000000 : ℝ)|=(518396603/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1297523013/10000000000 : ℝ)|^4389 ≤ (174248061343/2500000000000 : ℝ)^3365
        have hw : |(-1297523013/10000000000 : ℝ)|=(1297523013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(46330193/78125000 : ℝ)|^4389 ≤ (6323077100767/12500000000000 : ℝ)^3365
        have hw : |(46330193/78125000 : ℝ)|=(46330193/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1429_s0_6 (p : ℝ) (hpa : (1097/256 : ℝ) ≤ p) (hpb : p ≤ (4389/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (103679321/200000000 : ℝ)*x 0 + (5930264543/10000000000 : ℝ)*x 1 + (-1297523237/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (103679321/200000000 : ℝ)^4389 ≤ (42445460942447/100000000000000 : ℝ)^3365 := by
    have hnat : (103679321 : ℕ)^4389*100000000000000^3365 ≤ 42445460942447^3365*200000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      103679321 200000000 42445460942447 100000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5930264543/10000000000 : ℝ)^4389 ≤ (12646153753727/25000000000000 : ℝ)^3365 := by
    have hnat : (5930264543 : ℕ)^4389*25000000000000^3365 ≤ 12646153753727^3365*10000000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5930264543 10000000000 12646153753727 25000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1297523237/10000000000 : ℝ)^4389 ≤ (1742481005787/25000000000000 : ℝ)^3365 := by
    have hnat : (1297523237 : ℕ)^4389*25000000000000^3365 ≤ 1742481005787^3365*10000000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1297523237 10000000000 1742481005787 25000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4389/1024 : ℝ)) 4389 3365 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(103679321/200000000 : ℝ), (5930264543/10000000000 : ℝ), (-1297523237/10000000000 : ℝ)] ![(42445460942447/100000000000000 : ℝ), (12646153753727/25000000000000 : ℝ), (1742481005787/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(103679321/200000000 : ℝ)|^4389 ≤ (42445460942447/100000000000000 : ℝ)^3365
        have hw : |(103679321/200000000 : ℝ)|=(103679321/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5930264543/10000000000 : ℝ)|^4389 ≤ (12646153753727/25000000000000 : ℝ)^3365
        have hw : |(5930264543/10000000000 : ℝ)|=(5930264543/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1297523237/10000000000 : ℝ)|^4389 ≤ (1742481005787/25000000000000 : ℝ)^3365
        have hw : |(-1297523237/10000000000 : ℝ)|=(1297523237/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1429_s0_7 (p : ℝ) (hpa : (1097/256 : ℝ) ≤ p) (hpb : p ≤ (4389/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (166987729/400000000 : ℝ)*x 0 + (5483150073/10000000000 : ℝ)*x 1 + (316807633/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (166987729/400000000 : ℝ)^4389 ≤ (32002004670267/100000000000000 : ℝ)^3365 := by
    have hnat : (166987729 : ℕ)^4389*100000000000000^3365 ≤ 32002004670267^3365*400000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      166987729 400000000 32002004670267 100000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5483150073/10000000000 : ℝ)^4389 ≤ (45668278049481/100000000000000 : ℝ)^3365 := by
    have hnat : (5483150073 : ℕ)^4389*100000000000000^3365 ≤ 45668278049481^3365*10000000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5483150073 10000000000 45668278049481 100000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (316807633/1000000000 : ℝ)^4389 ≤ (22329717269239/100000000000000 : ℝ)^3365 := by
    have hnat : (316807633 : ℕ)^4389*100000000000000^3365 ≤ 22329717269239^3365*1000000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      316807633 1000000000 22329717269239 100000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4389/1024 : ℝ)) 4389 3365 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(166987729/400000000 : ℝ), (5483150073/10000000000 : ℝ), (316807633/1000000000 : ℝ)] ![(32002004670267/100000000000000 : ℝ), (45668278049481/100000000000000 : ℝ), (22329717269239/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(166987729/400000000 : ℝ)|^4389 ≤ (32002004670267/100000000000000 : ℝ)^3365
        have hw : |(166987729/400000000 : ℝ)|=(166987729/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5483150073/10000000000 : ℝ)|^4389 ≤ (45668278049481/100000000000000 : ℝ)^3365
        have hw : |(5483150073/10000000000 : ℝ)|=(5483150073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(316807633/1000000000 : ℝ)|^4389 ≤ (22329717269239/100000000000000 : ℝ)^3365
        have hw : |(316807633/1000000000 : ℝ)|=(316807633/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1429_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1097/256 : ℝ) ≤ p) (hpb : p ≤ (4389/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158166723/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (64/3125 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (13129/50000 : ℝ)*pair X 0 0 := by
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
  have base32 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1+(1 : ℝ)*X 2 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 1).2]
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
  have hpowlo : (0 : ℝ) ^ (1097/256 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^1097 ≤ (0 : ℝ)^256 := by
      have hnat : (0 : ℕ)^1097*1^256 ≤ 0^256*1^1097 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 1097 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 1097 256 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (1097/256 : ℝ) ≤ (394271041757078559/20000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^1097 ≤ (394271041757078559/20000000000000000000 : ℝ)^256 := by
      have hnat : (2 : ℕ)^1097*20000000000000000000^256 ≤ 394271041757078559^256*5^1097 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 394271041757078559 20000000000000000000 1097 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (394271041757078559/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1097 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (1097/256 : ℝ) := by
    have hpowers : (1 : ℝ)^256 ≤ (1 : ℝ)^1097 := by
      have hnat : (1 : ℕ)^256*1^1097 ≤ 1^1097*1^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 256 1097 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 1097 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (20394271041757078559/20000000000000000000 : ℝ) ≤ (10045660625584071/10000000000000000 : ℝ) ^ (1097/256 : ℝ) := by
    have hpowers : (20394271041757078559/20000000000000000000 : ℝ)^256 ≤ (10045660625584071/10000000000000000 : ℝ)^1097 := by
      have hnat : (20394271041757078559 : ℕ)^256*10000000000000000^1097 ≤ 10045660625584071^1097*20000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20394271041757078559 20000000000000000000 10045660625584071 10000000000000000 256 1097 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10045660625584071/10000000000000000 : ℝ)) (X := (20394271041757078559/20000000000000000000 : ℝ)) (by norm_num) 1097 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (10394271041757078559/10000000000000000000 : ℝ) ≤ (5045660625584071/5000000000000000 : ℝ) ^ (1097/256 : ℝ) := by
    have hpowers : (10394271041757078559/10000000000000000000 : ℝ)^256 ≤ (5045660625584071/5000000000000000 : ℝ)^1097 := by
      have hnat : (10394271041757078559 : ℕ)^256*5000000000000000^1097 ≤ 5045660625584071^1097*10000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10394271041757078559 10000000000000000000 5045660625584071 5000000000000000 256 1097 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5045660625584071/5000000000000000 : ℝ)) (X := (10394271041757078559/10000000000000000000 : ℝ)) (by norm_num) 1097 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(45660625584071/4000000000000000 : ℝ)*(0 : ℝ))^(1097/256 : ℝ) := by
    rw [show (1 : ℝ)+2*(45660625584071/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(394271041757078559/20000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(45660625584071/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(1097/256 : ℝ) := by
    rw [show (1 : ℝ)+(45660625584071/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10045660625584071/10000000000000000 : ℝ) by norm_num, show 1+(394271041757078559/20000000000000000000 : ℝ)+(0 : ℝ)=(20394271041757078559/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(394271041757078559/20000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(45660625584071/4000000000000000 : ℝ)*(2/5 : ℝ))^(1097/256 : ℝ) := by
    rw [show (1 : ℝ)+2*(45660625584071/4000000000000000 : ℝ)*(2/5 : ℝ)=(5045660625584071/5000000000000000 : ℝ) by norm_num, show 1+2*(394271041757078559/20000000000000000000 : ℝ)=(10394271041757078559/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(45660625584071/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1097/256 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (45660625584071/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(45660625584071/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1097/256 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (45660625584071/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(45660625584071/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1097/256 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (45660625584071/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-219851731/1250000000 : ℝ)*X 0 0+(149004523/250000000 : ℝ)*X 0 1+(2415619057/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1429_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((43936793/80000000 : ℝ)*X 1 0+(-1198274889/5000000000 : ℝ)*X 1 1+(966247711/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1429_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1098419931/2000000000 : ℝ)*X 2 0+(2415619183/5000000000 : ℝ)*X 2 1+(-2396549331/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1429_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2083000269/5000000000 : ℝ)*X 0 0+(620671359/2000000000 : ℝ)*X 0 1+(1109127693/2000000000 : ℝ)*X 0 2+(2083000269/5000000000 : ℝ)*X 1 0+(620671359/2000000000 : ℝ)*X 1 1+(1109127693/2000000000 : ℝ)*X 1 2+(2083000269/5000000000 : ℝ)*X 2 0+(620671359/2000000000 : ℝ)*X 2 1+(1109127693/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1429_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-176283099/1000000000 : ℝ)*X 0 0+(4860123187/10000000000 : ℝ)*X 0 1+(593026463/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1429_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((518396603/1000000000 : ℝ)*X 1 0+(-1297523013/10000000000 : ℝ)*X 1 1+(46330193/78125000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1429_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((103679321/200000000 : ℝ)*X 2 0+(5930264543/10000000000 : ℝ)*X 2 1+(-1297523237/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1429_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((166987729/400000000 : ℝ)*X 0 0+(5483150073/10000000000 : ℝ)*X 0 1+(316807633/1000000000 : ℝ)*X 0 2+(166987729/400000000 : ℝ)*X 1 0+(5483150073/10000000000 : ℝ)*X 1 1+(316807633/1000000000 : ℝ)*X 1 2+(166987729/400000000 : ℝ)*X 2 0+(5483150073/10000000000 : ℝ)*X 2 1+(316807633/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1429_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (8517637912783542134001/4000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (634863759/100000000000000 : ℝ)*(base19) + (77538253/12500000000000 : ℝ)*(base23) + (62429579/100000000000000 : ℝ)*(upper3) + (10988409/20000000000000 : ℝ)*(upper4) + (118790883/100000000000000 : ℝ)*(upper5) + (64762236932723/10000000000000 : ℝ)*(major0) + (64762236932723/10000000000000 : ℝ)*(major1) + (64762236932723/10000000000000 : ℝ)*(major2) + (110723297507393/12500000000000 : ℝ)*(sp0) + (885788518373737/100000000000000 : ℝ)*(sp1) + (55361783308217/6250000000000 : ℝ)*(sp2) + (204727179687881/50000000000000 : ℝ)*(sp3) + (2773178353/100000000000000 : ℝ)*(sp4) + (14438261/1250000000000 : ℝ)*(sp7) + (409455514436643/100000000000000 : ℝ)*(f.failure) + (110723644154687/12500000000000 : ℝ)*(f.sum) + (58761159975333/20000000000000000000000000000 : ℝ)*base65 + (4162613384667/40000000000000000000000000000 : ℝ)*base68 + (106922426015333/40000000000000000000000000000 : ℝ)*base69 + (62204284215333/40000000000000000000000000000 : ℝ)*base71 + (97138074575333/20000000000000000000000000000 : ℝ)*base73 + (164951976855333/40000000000000000000000000000 : ℝ)*base75 + (217837802815333/40000000000000000000000000000 : ℝ)*base77 + (62511336175333/40000000000000000000000000000 : ℝ)*base79 + (117971197495333/20000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (14430889/10000000000000000000000 : ℝ)*base89 + (14430889/10000000000000000000000 : ℝ)*base91 + (14430889/10000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (264110361402850820660637/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (300582429/25000000000000 : ℝ)*(base19) + (1211475083/100000000000000 : ℝ)*(base23) + (69314439/50000000000000 : ℝ)*(base32) + (184685139/100000000000000 : ℝ)*(upper3) + (49380829/50000000000000 : ℝ)*(upper5) + (170800869136483/25000000000000 : ℝ)*(major0) + (170800869136483/25000000000000 : ℝ)*(major1) + (170800869136483/25000000000000 : ℝ)*(major2) + (1417373913/50000000000000 : ℝ)*(sp1) + (2927950081/100000000000000 : ℝ)*(sp2) + (93445531239451/10000000000000 : ℝ)*(sp4) + (116806409414621/12500000000000 : ℝ)*(sp5) + (467225586484673/50000000000000 : ℝ)*(sp6) + (431951325994899/100000000000000 : ℝ)*(sp7) + (431951464623777/100000000000000 : ℝ)*(f.failure) + (93445531239451/10000000000000 : ℝ)*(f.sum) + (36780428987707/50000000000000000000000000000 : ℝ)*base66 + (79321190062293/100000000000000000000000000000 : ℝ)*base67 + (589662907237707/100000000000000000000000000000 : ℝ)*base70 + (298048433262293/100000000000000000000000000000 : ℝ)*base71 + (107171230987707/50000000000000000000000000000 : ℝ)*base74 + (505377667437707/100000000000000000000000000000 : ℝ)*base76 + (27330826762293/100000000000000000000000000000 : ℝ)*base77 + (33399125337707/100000000000000000000000000000 : ℝ)*base80 + (275330803087707/50000000000000000000000000000 : ℝ)*base82 + (35972771/10000000000000000000000 : ℝ)*base89 + (35972771/10000000000000000000000 : ℝ)*base91 + (35972771/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1429_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1097/256 : ℝ) ≤ p) (hpb : p ≤ (4389/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158166723/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (64/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (13129/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1429_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1429_s1_0 (p : ℝ) (hpa : (1097/256 : ℝ) ≤ p) (hpb : p ≤ (4389/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-120698109/625000000 : ℝ)*x 0 + (2802611173/5000000000 : ℝ)*x 1 + (5075703083/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (120698109/625000000 : ℝ)^4389 ≤ (585408659381/5000000000000 : ℝ)^3365 := by
    have hnat : (120698109 : ℕ)^4389*5000000000000^3365 ≤ 585408659381^3365*625000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      120698109 625000000 585408659381 5000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2802611173/5000000000 : ℝ)^4389 ≤ (46998864845679/100000000000000 : ℝ)^3365 := by
    have hnat : (2802611173 : ℕ)^4389*100000000000000^3365 ≤ 46998864845679^3365*5000000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2802611173 5000000000 46998864845679 100000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5075703083/10000000000 : ℝ)^4389 ≤ (41292961946643/100000000000000 : ℝ)^3365 := by
    have hnat : (5075703083 : ℕ)^4389*100000000000000^3365 ≤ 41292961946643^3365*10000000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5075703083 10000000000 41292961946643 100000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4389/1024 : ℝ)) 4389 3365 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-120698109/625000000 : ℝ), (2802611173/5000000000 : ℝ), (5075703083/10000000000 : ℝ)] ![(585408659381/5000000000000 : ℝ), (46998864845679/100000000000000 : ℝ), (41292961946643/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-120698109/625000000 : ℝ)|^4389 ≤ (585408659381/5000000000000 : ℝ)^3365
        have hw : |(-120698109/625000000 : ℝ)|=(120698109/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2802611173/5000000000 : ℝ)|^4389 ≤ (46998864845679/100000000000000 : ℝ)^3365
        have hw : |(2802611173/5000000000 : ℝ)|=(2802611173/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5075703083/10000000000 : ℝ)|^4389 ≤ (41292961946643/100000000000000 : ℝ)^3365
        have hw : |(5075703083/10000000000 : ℝ)|=(5075703083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1429_s1_1 (p : ℝ) (hpa : (1097/256 : ℝ) ≤ p) (hpb : p ≤ (4389/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2698404627/5000000000 : ℝ)*x 0 + (-34558669/156250000 : ℝ)*x 1 + (5075704471/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2698404627/5000000000 : ℝ)^4389 ≤ (22366290170637/50000000000000 : ℝ)^3365 := by
    have hnat : (2698404627 : ℕ)^4389*50000000000000^3365 ≤ 22366290170637^3365*5000000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2698404627 5000000000 22366290170637 50000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (34558669/156250000 : ℝ)^4389 ≤ (13974442976903/100000000000000 : ℝ)^3365 := by
    have hnat : (34558669 : ℕ)^4389*100000000000000^3365 ≤ 13974442976903^3365*156250000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      34558669 156250000 13974442976903 100000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5075704471/10000000000 : ℝ)^4389 ≤ (1290405521089/3125000000000 : ℝ)^3365 := by
    have hnat : (5075704471 : ℕ)^4389*3125000000000^3365 ≤ 1290405521089^3365*10000000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5075704471 10000000000 1290405521089 3125000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4389/1024 : ℝ)) 4389 3365 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2698404627/5000000000 : ℝ), (-34558669/156250000 : ℝ), (5075704471/10000000000 : ℝ)] ![(22366290170637/50000000000000 : ℝ), (13974442976903/100000000000000 : ℝ), (1290405521089/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2698404627/5000000000 : ℝ)|^4389 ≤ (22366290170637/50000000000000 : ℝ)^3365
        have hw : |(2698404627/5000000000 : ℝ)|=(2698404627/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-34558669/156250000 : ℝ)|^4389 ≤ (13974442976903/100000000000000 : ℝ)^3365
        have hw : |(-34558669/156250000 : ℝ)|=(34558669/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5075704471/10000000000 : ℝ)|^4389 ≤ (1290405521089/3125000000000 : ℝ)^3365
        have hw : |(5075704471/10000000000 : ℝ)|=(5075704471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1429_s1_2 (p : ℝ) (hpa : (1097/256 : ℝ) ≤ p) (hpb : p ≤ (4389/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5396810323/10000000000 : ℝ)*x 0 + (5075703273/10000000000 : ℝ)*x 1 + (-442350991/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5396810323/10000000000 : ℝ)^4389 ≤ (22366295949137/50000000000000 : ℝ)^3365 := by
    have hnat : (5396810323 : ℕ)^4389*50000000000000^3365 ≤ 22366295949137^3365*10000000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5396810323 10000000000 22366295949137 50000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5075703273/10000000000 : ℝ)^4389 ≤ (41292963962751/100000000000000 : ℝ)^3365 := by
    have hnat : (5075703273 : ℕ)^4389*100000000000000^3365 ≤ 41292963962751^3365*10000000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5075703273 10000000000 41292963962751 100000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (442350991/2000000000 : ℝ)^4389 ≤ (13974444122397/100000000000000 : ℝ)^3365 := by
    have hnat : (442350991 : ℕ)^4389*100000000000000^3365 ≤ 13974444122397^3365*2000000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      442350991 2000000000 13974444122397 100000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4389/1024 : ℝ)) 4389 3365 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5396810323/10000000000 : ℝ), (5075703273/10000000000 : ℝ), (-442350991/2000000000 : ℝ)] ![(22366295949137/50000000000000 : ℝ), (41292963962751/100000000000000 : ℝ), (13974444122397/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5396810323/10000000000 : ℝ)|^4389 ≤ (22366295949137/50000000000000 : ℝ)^3365
        have hw : |(5396810323/10000000000 : ℝ)|=(5396810323/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5075703273/10000000000 : ℝ)|^4389 ≤ (41292963962751/100000000000000 : ℝ)^3365
        have hw : |(5075703273/10000000000 : ℝ)|=(5075703273/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-442350991/2000000000 : ℝ)|^4389 ≤ (13974444122397/100000000000000 : ℝ)^3365
        have hw : |(-442350991/2000000000 : ℝ)|=(442350991/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1429_s1_3 (p : ℝ) (hpa : (1097/256 : ℝ) ≤ p) (hpb : p ≤ (4389/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2138319643/5000000000 : ℝ)*x 0 + (3738115621/10000000000 : ℝ)*x 1 + (76306881/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2138319643/5000000000 : ℝ)^4389 ≤ (33025074432979/100000000000000 : ℝ)^3365 := by
    have hnat : (2138319643 : ℕ)^4389*100000000000000^3365 ≤ 33025074432979^3365*5000000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2138319643 5000000000 33025074432979 100000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3738115621/10000000000 : ℝ)^4389 ≤ (5541624288481/20000000000000 : ℝ)^3365 := by
    have hnat : (3738115621 : ℕ)^4389*20000000000000^3365 ≤ 5541624288481^3365*10000000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3738115621 10000000000 5541624288481 20000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (76306881/156250000 : ℝ)^4389 ≤ (9816701027873/25000000000000 : ℝ)^3365 := by
    have hnat : (76306881 : ℕ)^4389*25000000000000^3365 ≤ 9816701027873^3365*156250000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      76306881 156250000 9816701027873 25000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4389/1024 : ℝ)) 4389 3365 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2138319643/5000000000 : ℝ), (3738115621/10000000000 : ℝ), (76306881/156250000 : ℝ)] ![(33025074432979/100000000000000 : ℝ), (5541624288481/20000000000000 : ℝ), (9816701027873/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2138319643/5000000000 : ℝ)|^4389 ≤ (33025074432979/100000000000000 : ℝ)^3365
        have hw : |(2138319643/5000000000 : ℝ)|=(2138319643/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3738115621/10000000000 : ℝ)|^4389 ≤ (5541624288481/20000000000000 : ℝ)^3365
        have hw : |(3738115621/10000000000 : ℝ)|=(3738115621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(76306881/156250000 : ℝ)|^4389 ≤ (9816701027873/25000000000000 : ℝ)^3365
        have hw : |(76306881/156250000 : ℝ)|=(76306881/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1429_s1_4 (p : ℝ) (hpa : (1097/256 : ℝ) ≤ p) (hpb : p ≤ (4389/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-965783847/5000000000 : ℝ)*x 0 + (158809761/312500000 : ℝ)*x 1 + (2799453913/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (965783847/5000000000 : ℝ)^4389 ≤ (2927830037093/25000000000000 : ℝ)^3365 := by
    have hnat : (965783847 : ℕ)^4389*25000000000000^3365 ≤ 2927830037093^3365*5000000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      965783847 5000000000 2927830037093 25000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (158809761/312500000 : ℝ)^4389 ≤ (41358861371063/100000000000000 : ℝ)^3365 := by
    have hnat : (158809761 : ℕ)^4389*100000000000000^3365 ≤ 41358861371063^3365*312500000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      158809761 312500000 41358861371063 100000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2799453913/5000000000 : ℝ)^4389 ≤ (5866227308257/12500000000000 : ℝ)^3365 := by
    have hnat : (2799453913 : ℕ)^4389*12500000000000^3365 ≤ 5866227308257^3365*5000000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2799453913 5000000000 5866227308257 12500000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4389/1024 : ℝ)) 4389 3365 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-965783847/5000000000 : ℝ), (158809761/312500000 : ℝ), (2799453913/5000000000 : ℝ)] ![(2927830037093/25000000000000 : ℝ), (41358861371063/100000000000000 : ℝ), (5866227308257/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-965783847/5000000000 : ℝ)|^4389 ≤ (2927830037093/25000000000000 : ℝ)^3365
        have hw : |(-965783847/5000000000 : ℝ)|=(965783847/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(158809761/312500000 : ℝ)|^4389 ≤ (41358861371063/100000000000000 : ℝ)^3365
        have hw : |(158809761/312500000 : ℝ)|=(158809761/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2799453913/5000000000 : ℝ)|^4389 ≤ (5866227308257/12500000000000 : ℝ)^3365
        have hw : |(2799453913/5000000000 : ℝ)|=(2799453913/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1429_s1_5 (p : ℝ) (hpa : (1097/256 : ℝ) ≤ p) (hpb : p ≤ (4389/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5258460649/10000000000 : ℝ)*x 0 + (-422137711/2500000000 : ℝ)*x 1 + (5598907841/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5258460649/10000000000 : ℝ)^4389 ≤ (43242757355329/100000000000000 : ℝ)^3365 := by
    have hnat : (5258460649 : ℕ)^4389*100000000000000^3365 ≤ 43242757355329^3365*10000000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5258460649 10000000000 43242757355329 100000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (422137711/2500000000 : ℝ)^4389 ≤ (4913712000727/50000000000000 : ℝ)^3365 := by
    have hnat : (422137711 : ℕ)^4389*50000000000000^3365 ≤ 4913712000727^3365*2500000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      422137711 2500000000 4913712000727 50000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5598907841/10000000000 : ℝ)^4389 ≤ (23464909315023/50000000000000 : ℝ)^3365 := by
    have hnat : (5598907841 : ℕ)^4389*50000000000000^3365 ≤ 23464909315023^3365*10000000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5598907841 10000000000 23464909315023 50000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4389/1024 : ℝ)) 4389 3365 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5258460649/10000000000 : ℝ), (-422137711/2500000000 : ℝ), (5598907841/10000000000 : ℝ)] ![(43242757355329/100000000000000 : ℝ), (4913712000727/50000000000000 : ℝ), (23464909315023/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5258460649/10000000000 : ℝ)|^4389 ≤ (43242757355329/100000000000000 : ℝ)^3365
        have hw : |(5258460649/10000000000 : ℝ)|=(5258460649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-422137711/2500000000 : ℝ)|^4389 ≤ (4913712000727/50000000000000 : ℝ)^3365
        have hw : |(-422137711/2500000000 : ℝ)|=(422137711/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5598907841/10000000000 : ℝ)|^4389 ≤ (23464909315023/50000000000000 : ℝ)^3365
        have hw : |(5598907841/10000000000 : ℝ)|=(5598907841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1429_s1_6 (p : ℝ) (hpa : (1097/256 : ℝ) ≤ p) (hpb : p ≤ (4389/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5258460601/10000000000 : ℝ)*x 0 + (5598907803/10000000000 : ℝ)*x 1 + (-844275483/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5258460601/10000000000 : ℝ)^4389 ≤ (10810689210121/25000000000000 : ℝ)^3365 := by
    have hnat : (5258460601 : ℕ)^4389*25000000000000^3365 ≤ 10810689210121^3365*10000000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5258460601 10000000000 10810689210121 25000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5598907803/10000000000 : ℝ)^4389 ≤ (11732454553651/25000000000000 : ℝ)^3365 := by
    have hnat : (5598907803 : ℕ)^4389*25000000000000^3365 ≤ 11732454553651^3365*10000000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5598907803 10000000000 11732454553651 25000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (844275483/5000000000 : ℝ)^4389 ≤ (9827424927571/100000000000000 : ℝ)^3365 := by
    have hnat : (844275483 : ℕ)^4389*100000000000000^3365 ≤ 9827424927571^3365*5000000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      844275483 5000000000 9827424927571 100000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4389/1024 : ℝ)) 4389 3365 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5258460601/10000000000 : ℝ), (5598907803/10000000000 : ℝ), (-844275483/5000000000 : ℝ)] ![(10810689210121/25000000000000 : ℝ), (11732454553651/25000000000000 : ℝ), (9827424927571/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5258460601/10000000000 : ℝ)|^4389 ≤ (10810689210121/25000000000000 : ℝ)^3365
        have hw : |(5258460601/10000000000 : ℝ)|=(5258460601/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5598907803/10000000000 : ℝ)|^4389 ≤ (11732454553651/25000000000000 : ℝ)^3365
        have hw : |(5598907803/10000000000 : ℝ)|=(5598907803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-844275483/5000000000 : ℝ)|^4389 ≤ (9827424927571/100000000000000 : ℝ)^3365
        have hw : |(-844275483/5000000000 : ℝ)|=(844275483/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1429_s1_7 (p : ℝ) (hpa : (1097/256 : ℝ) ≤ p) (hpb : p ≤ (4389/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (427750071/1000000000 : ℝ)*x 0 + (4870208747/10000000000 : ℝ)*x 1 + (937943591/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (427750071/1000000000 : ℝ)^4389 ≤ (16516875540429/50000000000000 : ℝ)^3365 := by
    have hnat : (427750071 : ℕ)^4389*50000000000000^3365 ≤ 16516875540429^3365*1000000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      427750071 1000000000 16516875540429 50000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4870208747/10000000000 : ℝ)^4389 ≤ (39126001910983/100000000000000 : ℝ)^3365 := by
    have hnat : (4870208747 : ℕ)^4389*100000000000000^3365 ≤ 39126001910983^3365*10000000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4870208747 10000000000 39126001910983 100000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (937943591/2500000000 : ℝ)^4389 ≤ (2784024698289/10000000000000 : ℝ)^3365 := by
    have hnat : (937943591 : ℕ)^4389*10000000000000^3365 ≤ 2784024698289^3365*2500000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      937943591 2500000000 2784024698289 10000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4389/1024 : ℝ)) 4389 3365 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(427750071/1000000000 : ℝ), (4870208747/10000000000 : ℝ), (937943591/2500000000 : ℝ)] ![(16516875540429/50000000000000 : ℝ), (39126001910983/100000000000000 : ℝ), (2784024698289/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(427750071/1000000000 : ℝ)|^4389 ≤ (16516875540429/50000000000000 : ℝ)^3365
        have hw : |(427750071/1000000000 : ℝ)|=(427750071/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4870208747/10000000000 : ℝ)|^4389 ≤ (39126001910983/100000000000000 : ℝ)^3365
        have hw : |(4870208747/10000000000 : ℝ)|=(4870208747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(937943591/2500000000 : ℝ)|^4389 ≤ (2784024698289/10000000000000 : ℝ)^3365
        have hw : |(937943591/2500000000 : ℝ)|=(937943591/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1429_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1097/256 : ℝ) ≤ p) (hpb : p ≤ (4389/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158166723/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13129/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (64/3125 : ℝ)*pair X i i ≤ pair X i h) :
    (1913/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (9423/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (13129/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (64/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (13129/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (64/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (13129/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (64/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (13129/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (64/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (13129/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (64/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (13129/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (64/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base1 : ((1 : ℝ)*N 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 0]
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
  have hpowlo : (64/3125 : ℝ) ^ (1097/256 : ℝ) ≤ (5804769657589/100000000000000000000 : ℝ) := by
    have hpowers : (64/3125 : ℝ)^1097 ≤ (5804769657589/100000000000000000000 : ℝ)^256 := by
      have hnat : (64 : ℕ)^1097*100000000000000000000^256 ≤ 5804769657589^256*3125^1097 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        64 3125 5804769657589 100000000000000000000 1097 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (64/3125 : ℝ)) (X := (5804769657589/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1097 256 (by norm_num) hpowers
    exact h
  have hpowhi : (13129/50000 : ℝ) ^ (1097/256 : ℝ) ≤ (20292026531434433/6250000000000000000 : ℝ) := by
    have hpowers : (13129/50000 : ℝ)^1097 ≤ (20292026531434433/6250000000000000000 : ℝ)^256 := by
      have hnat : (13129 : ℕ)^1097*6250000000000000000^256 ≤ 20292026531434433^256*50000^1097 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13129 50000 20292026531434433 6250000000000000000 1097 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (13129/50000 : ℝ)) (X := (20292026531434433/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 1097 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000005804769657589/50000000000000000000 : ℝ) ≤ (2500000067731129/2500000000000000 : ℝ) ^ (1097/256 : ℝ) := by
    have hpowers : (50000005804769657589/50000000000000000000 : ℝ)^256 ≤ (2500000067731129/2500000000000000 : ℝ)^1097 := by
      have hnat : (50000005804769657589 : ℕ)^256*2500000000000000^1097 ≤ 2500000067731129^1097*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000005804769657589 50000000000000000000 2500000067731129 2500000000000000 256 1097 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500000067731129/2500000000000000 : ℝ)) (X := (50000005804769657589/50000000000000000000 : ℝ)) (by norm_num) 1097 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (100324678229272608517/100000000000000000000 : ℝ) ≤ (5003783700088593/5000000000000000 : ℝ) ^ (1097/256 : ℝ) := by
    have hpowers : (100324678229272608517/100000000000000000000 : ℝ)^256 ≤ (5003783700088593/5000000000000000 : ℝ)^1097 := by
      have hnat : (100324678229272608517 : ℕ)^256*5000000000000000^1097 ≤ 5003783700088593^1097*100000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100324678229272608517 100000000000000000000 5003783700088593 5000000000000000 256 1097 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5003783700088593/5000000000000000 : ℝ)) (X := (100324678229272608517/100000000000000000000 : ℝ)) (by norm_num) 1097 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (3145292026531434433/3125000000000000000 : ℝ) ≤ (312972954044683/312500000000000 : ℝ) ^ (1097/256 : ℝ) := by
    have hpowers : (3145292026531434433/3125000000000000000 : ℝ)^256 ≤ (312972954044683/312500000000000 : ℝ)^1097 := by
      have hnat : (3145292026531434433 : ℕ)^256*312500000000000^1097 ≤ 312972954044683^1097*3125000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3145292026531434433 3125000000000000000 312972954044683 312500000000000 256 1097 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312972954044683/312500000000000 : ℝ)) (X := (3145292026531434433/3125000000000000000 : ℝ)) (by norm_num) 1097 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5804769657589/100000000000000000000 : ℝ) ≤ ((6051725289941589901/6052500000000000000 : ℝ)+2*(756712925267/242100000000000 : ℝ)*(64/3125 : ℝ))^(1097/256 : ℝ) := by
    rw [show (6051725289941589901/6052500000000000000 : ℝ)+2*(756712925267/242100000000000 : ℝ)*(64/3125 : ℝ)=(2500000067731129/2500000000000000 : ℝ) by norm_num, show 1+2*(5804769657589/100000000000000000000 : ℝ)=(50000005804769657589/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(20292026531434433/6250000000000000000 : ℝ)+(5804769657589/100000000000000000000 : ℝ) ≤ ((6051725289941589901/6052500000000000000 : ℝ)+(756712925267/242100000000000 : ℝ)*((13129/50000 : ℝ)+(64/3125 : ℝ)))^(1097/256 : ℝ) := by
    rw [show (6051725289941589901/6052500000000000000 : ℝ)+(756712925267/242100000000000 : ℝ)*((13129/50000 : ℝ)+(64/3125 : ℝ))=(5003783700088593/5000000000000000 : ℝ) by norm_num, show 1+(20292026531434433/6250000000000000000 : ℝ)+(5804769657589/100000000000000000000 : ℝ)=(100324678229272608517/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(20292026531434433/6250000000000000000 : ℝ) ≤ ((6051725289941589901/6052500000000000000 : ℝ)+2*(756712925267/242100000000000 : ℝ)*(13129/50000 : ℝ))^(1097/256 : ℝ) := by
    rw [show (6051725289941589901/6052500000000000000 : ℝ)+2*(756712925267/242100000000000 : ℝ)*(13129/50000 : ℝ)=(312972954044683/312500000000000 : ℝ) by norm_num, show 1+2*(20292026531434433/6250000000000000000 : ℝ)=(3145292026531434433/3125000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6051725289941589901/6052500000000000000 : ℝ)*(X 1 0+X 2 0)+(756712925267/242100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1097/256 : ℝ)) (lo := (64/3125 : ℝ)) (hi := (13129/50000 : ℝ)) (c := (6051725289941589901/6052500000000000000 : ℝ)) (alpha := (756712925267/242100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6051725289941589901/6052500000000000000 : ℝ)*(X 0 1+X 2 1)+(756712925267/242100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1097/256 : ℝ)) (lo := (64/3125 : ℝ)) (hi := (13129/50000 : ℝ)) (c := (6051725289941589901/6052500000000000000 : ℝ)) (alpha := (756712925267/242100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6051725289941589901/6052500000000000000 : ℝ)*(X 0 2+X 1 2)+(756712925267/242100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1097/256 : ℝ)) (lo := (64/3125 : ℝ)) (hi := (13129/50000 : ℝ)) (c := (6051725289941589901/6052500000000000000 : ℝ)) (alpha := (756712925267/242100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-120698109/625000000 : ℝ)*X 0 0+(2802611173/5000000000 : ℝ)*X 0 1+(5075703083/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1429_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2698404627/5000000000 : ℝ)*X 1 0+(-34558669/156250000 : ℝ)*X 1 1+(5075704471/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1429_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5396810323/10000000000 : ℝ)*X 2 0+(5075703273/10000000000 : ℝ)*X 2 1+(-442350991/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1429_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2138319643/5000000000 : ℝ)*X 0 0+(3738115621/10000000000 : ℝ)*X 0 1+(76306881/156250000 : ℝ)*X 0 2+(2138319643/5000000000 : ℝ)*X 1 0+(3738115621/10000000000 : ℝ)*X 1 1+(76306881/156250000 : ℝ)*X 1 2+(2138319643/5000000000 : ℝ)*X 2 0+(3738115621/10000000000 : ℝ)*X 2 1+(76306881/156250000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1429_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-965783847/5000000000 : ℝ)*X 0 0+(158809761/312500000 : ℝ)*X 0 1+(2799453913/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1429_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5258460649/10000000000 : ℝ)*X 1 0+(-422137711/2500000000 : ℝ)*X 1 1+(5598907841/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1429_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5258460601/10000000000 : ℝ)*X 2 0+(5598907803/10000000000 : ℝ)*X 2 1+(-844275483/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1429_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((427750071/1000000000 : ℝ)*X 0 0+(4870208747/10000000000 : ℝ)*X 0 1+(937943591/2500000000 : ℝ)*X 0 2+(427750071/1000000000 : ℝ)*X 1 0+(4870208747/10000000000 : ℝ)*X 1 1+(937943591/2500000000 : ℝ)*X 1 2+(427750071/1000000000 : ℝ)*X 2 0+(4870208747/10000000000 : ℝ)*X 2 1+(937943591/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1429_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (20143741245250881484499503/6304687500000000000000000000000 : ℝ) := by norm_num
    linear_combination (108374613/25000000000000 : ℝ)*(base19) + (744282143/100000000000000 : ℝ)*(base23) + (30943561/50000000000000 : ℝ)*(upper3) + (34158703/100000000000000 : ℝ)*(upper4) + (8098487/25000000000000 : ℝ)*(upper5) + (172592979563827/12500000000000 : ℝ)*(major0) + (172592979563827/12500000000000 : ℝ)*(major1) + (172592979563827/12500000000000 : ℝ)*(major2) + (47212807952547/2500000000000 : ℝ)*(sp0) + (188851979177437/10000000000000 : ℝ)*(sp1) + (1888519480990679/100000000000000 : ℝ)*(sp2) + (436482251319277/50000000000000 : ℝ)*(sp3) + (3953585471/50000000000000 : ℝ)*(sp4) + (709652113/25000000000000 : ℝ)*(sp7) + (436483670623503/50000000000000 : ℝ)*(f.failure) + (944260112636411/50000000000000 : ℝ)*(f.sum) + (4755040142701/1513125000000000000000000000 : ℝ)*base66 + (19747226838594597/8406250000000000000000000000000 : ℝ)*base68 + (52598092367532097/8406250000000000000000000000000 : ℝ)*base70 + (47585243305407097/8406250000000000000000000000000 : ℝ)*base72 + (18738064941941/6052500000000000000000000000 : ℝ)*base73 + (62051089777594597/8406250000000000000000000000000 : ℝ)*base76 + (10580588982063347/8406250000000000000000000000000 : ℝ)*base78 + (45612470448188347/8406250000000000000000000000000 : ℝ)*base80 + (50891690299523/12105000000000000000000000000 : ℝ)*base82 + (36290669/5000000000000000000000 : ℝ)*base89 + (36290669/5000000000000000000000 : ℝ)*base91 + (36290669/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (198785054803427948331221233/50437500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (5263803/20000000000000 : ℝ)*(base1) + (218830009/25000000000000 : ℝ)*(base19) + (424861421/50000000000000 : ℝ)*(base23) + (100239253/100000000000000 : ℝ)*(upper3) + (79967867/100000000000000 : ℝ)*(upper5) + (1414179883442033/100000000000000 : ℝ)*(major0) + (1414179883442033/100000000000000 : ℝ)*(major1) + (1414179883442033/100000000000000 : ℝ)*(major2) + (2610483637/50000000000000 : ℝ)*(sp1) + (2459548833/50000000000000 : ℝ)*(sp2) + (967126286205959/50000000000000 : ℝ)*(sp4) + (1934246449805593/100000000000000 : ℝ)*(sp5) + (967123388636197/50000000000000 : ℝ)*(sp6) + (223526765774573/25000000000000 : ℝ)*(sp7) + (447053544708653/50000000000000 : ℝ)*(f.failure) + (1934252546092903/100000000000000 : ℝ)*(f.sum) + (8815489737871/12105000000000000000000000000 : ℝ)*base65 + (288127700447557363/67250000000000000000000000000000 : ℝ)*base68 + (553569186603557363/67250000000000000000000000000000 : ℝ)*base70 + (279168622696807363/67250000000000000000000000000000 : ℝ)*base72 + (7425983176771/12105000000000000000000000000 : ℝ)*base73 + (134868433661307363/67250000000000000000000000000000 : ℝ)*base76 + (693629798314557363/67250000000000000000000000000000 : ℝ)*base78 + (866572280248442637/67250000000000000000000000000000 : ℝ)*base79 + (55814417758859/12105000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (15245881/5000000000000000000000 : ℝ)*base90 + (15245881/5000000000000000000000 : ℝ)*base92 + (15245881/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1429_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1097/256 : ℝ) ≤ p) (hpb : p ≤ (4389/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158166723/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13129/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (64/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1913/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (9423/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1429_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1429_s2_0 (p : ℝ) (hpa : (1097/256 : ℝ) ≤ p) (hpb : p ≤ (4389/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-245537683/1250000000 : ℝ)*x 0 + (1364542033/2500000000 : ℝ)*x 1 + (2600715481/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (245537683/1250000000 : ℝ)^4389 ≤ (11970849509539/100000000000000 : ℝ)^3365 := by
    have hnat : (245537683 : ℕ)^4389*100000000000000^3365 ≤ 11970849509539^3365*1250000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      245537683 1250000000 11970849509539 100000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1364542033/2500000000 : ℝ)^4389 ≤ (45397078038489/100000000000000 : ℝ)^3365 := by
    have hnat : (1364542033 : ℕ)^4389*100000000000000^3365 ≤ 45397078038489^3365*2500000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1364542033 2500000000 45397078038489 100000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2600715481/5000000000 : ℝ)^4389 ≤ (426320724467/1000000000000 : ℝ)^3365 := by
    have hnat : (2600715481 : ℕ)^4389*1000000000000^3365 ≤ 426320724467^3365*5000000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2600715481 5000000000 426320724467 1000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4389/1024 : ℝ)) 4389 3365 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-245537683/1250000000 : ℝ), (1364542033/2500000000 : ℝ), (2600715481/5000000000 : ℝ)] ![(11970849509539/100000000000000 : ℝ), (45397078038489/100000000000000 : ℝ), (426320724467/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-245537683/1250000000 : ℝ)|^4389 ≤ (11970849509539/100000000000000 : ℝ)^3365
        have hw : |(-245537683/1250000000 : ℝ)|=(245537683/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1364542033/2500000000 : ℝ)|^4389 ≤ (45397078038489/100000000000000 : ℝ)^3365
        have hw : |(1364542033/2500000000 : ℝ)|=(1364542033/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2600715481/5000000000 : ℝ)|^4389 ≤ (426320724467/1000000000000 : ℝ)^3365
        have hw : |(2600715481/5000000000 : ℝ)|=(2600715481/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1429_s2_1 (p : ℝ) (hpa : (1097/256 : ℝ) ≤ p) (hpb : p ≤ (4389/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5360139499/10000000000 : ℝ)*x 0 + (-2096391443/10000000000 : ℝ)*x 1 + (2600715429/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5360139499/10000000000 : ℝ)^4389 ≤ (5542069091209/12500000000000 : ℝ)^3365 := by
    have hnat : (5360139499 : ℕ)^4389*12500000000000^3365 ≤ 5542069091209^3365*10000000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5360139499 10000000000 5542069091209 12500000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2096391443/10000000000 : ℝ)^4389 ≤ (6515687956701/50000000000000 : ℝ)^3365 := by
    have hnat : (2096391443 : ℕ)^4389*50000000000000^3365 ≤ 6515687956701^3365*10000000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2096391443 10000000000 6515687956701 50000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2600715429/5000000000 : ℝ)^4389 ≤ (21316035667449/50000000000000 : ℝ)^3365 := by
    have hnat : (2600715429 : ℕ)^4389*50000000000000^3365 ≤ 21316035667449^3365*5000000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2600715429 5000000000 21316035667449 50000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4389/1024 : ℝ)) 4389 3365 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5360139499/10000000000 : ℝ), (-2096391443/10000000000 : ℝ), (2600715429/5000000000 : ℝ)] ![(5542069091209/12500000000000 : ℝ), (6515687956701/50000000000000 : ℝ), (21316035667449/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5360139499/10000000000 : ℝ)|^4389 ≤ (5542069091209/12500000000000 : ℝ)^3365
        have hw : |(5360139499/10000000000 : ℝ)|=(5360139499/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2096391443/10000000000 : ℝ)|^4389 ≤ (6515687956701/50000000000000 : ℝ)^3365
        have hw : |(-2096391443/10000000000 : ℝ)|=(2096391443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2600715429/5000000000 : ℝ)|^4389 ≤ (21316035667449/50000000000000 : ℝ)^3365
        have hw : |(2600715429/5000000000 : ℝ)|=(2600715429/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1429_s2_2 (p : ℝ) (hpa : (1097/256 : ℝ) ≤ p) (hpb : p ≤ (4389/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2680069559/5000000000 : ℝ)*x 0 + (5201431291/10000000000 : ℝ)*x 1 + (-104819569/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2680069559/5000000000 : ℝ)^4389 ≤ (11084137154801/25000000000000 : ℝ)^3365 := by
    have hnat : (2680069559 : ℕ)^4389*25000000000000^3365 ≤ 11084137154801^3365*5000000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2680069559 5000000000 11084137154801 25000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5201431291/10000000000 : ℝ)^4389 ≤ (42632075963843/100000000000000 : ℝ)^3365 := by
    have hnat : (5201431291 : ℕ)^4389*100000000000000^3365 ≤ 42632075963843^3365*10000000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5201431291 10000000000 42632075963843 100000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (104819569/500000000 : ℝ)^4389 ≤ (1628921925327/12500000000000 : ℝ)^3365 := by
    have hnat : (104819569 : ℕ)^4389*12500000000000^3365 ≤ 1628921925327^3365*500000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      104819569 500000000 1628921925327 12500000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4389/1024 : ℝ)) 4389 3365 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2680069559/5000000000 : ℝ), (5201431291/10000000000 : ℝ), (-104819569/500000000 : ℝ)] ![(11084137154801/25000000000000 : ℝ), (42632075963843/100000000000000 : ℝ), (1628921925327/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2680069559/5000000000 : ℝ)|^4389 ≤ (11084137154801/25000000000000 : ℝ)^3365
        have hw : |(2680069559/5000000000 : ℝ)|=(2680069559/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5201431291/10000000000 : ℝ)|^4389 ≤ (42632075963843/100000000000000 : ℝ)^3365
        have hw : |(5201431291/10000000000 : ℝ)|=(5201431291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-104819569/500000000 : ℝ)|^4389 ≤ (1628921925327/12500000000000 : ℝ)^3365
        have hw : |(-104819569/500000000 : ℝ)|=(104819569/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1429_s2_3 (p : ℝ) (hpa : (1097/256 : ℝ) ≤ p) (hpb : p ≤ (4389/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2150013723/5000000000 : ℝ)*x 0 + (2015186429/5000000000 : ℝ)*x 1 + (1146445339/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2150013723/5000000000 : ℝ)^4389 ≤ (16630419496857/50000000000000 : ℝ)^3365 := by
    have hnat : (2150013723 : ℕ)^4389*50000000000000^3365 ≤ 16630419496857^3365*5000000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2150013723 5000000000 16630419496857 50000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2015186429/5000000000 : ℝ)^4389 ≤ (6113335015711/20000000000000 : ℝ)^3365 := by
    have hnat : (2015186429 : ℕ)^4389*20000000000000^3365 ≤ 6113335015711^3365*5000000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2015186429 5000000000 6113335015711 20000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1146445339/2500000000 : ℝ)^4389 ≤ (36172485902609/100000000000000 : ℝ)^3365 := by
    have hnat : (1146445339 : ℕ)^4389*100000000000000^3365 ≤ 36172485902609^3365*2500000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1146445339 2500000000 36172485902609 100000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4389/1024 : ℝ)) 4389 3365 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2150013723/5000000000 : ℝ), (2015186429/5000000000 : ℝ), (1146445339/2500000000 : ℝ)] ![(16630419496857/50000000000000 : ℝ), (6113335015711/20000000000000 : ℝ), (36172485902609/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2150013723/5000000000 : ℝ)|^4389 ≤ (16630419496857/50000000000000 : ℝ)^3365
        have hw : |(2150013723/5000000000 : ℝ)|=(2150013723/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2015186429/5000000000 : ℝ)|^4389 ≤ (6113335015711/20000000000000 : ℝ)^3365
        have hw : |(2015186429/5000000000 : ℝ)|=(2015186429/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1146445339/2500000000 : ℝ)|^4389 ≤ (36172485902609/100000000000000 : ℝ)^3365
        have hw : |(1146445339/2500000000 : ℝ)|=(1146445339/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1429_s2_4 (p : ℝ) (hpa : (1097/256 : ℝ) ≤ p) (hpb : p ≤ (4389/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-12277169/62500000 : ℝ)*x 0 + (5202899641/10000000000 : ℝ)*x 1 + (545668731/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (12277169/62500000 : ℝ)^4389 ≤ (11971211781801/100000000000000 : ℝ)^3365 := by
    have hnat : (12277169 : ℕ)^4389*100000000000000^3365 ≤ 11971211781801^3365*62500000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      12277169 62500000 11971211781801 100000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5202899641/10000000000 : ℝ)^4389 ≤ (5330971736637/12500000000000 : ℝ)^3365 := by
    have hnat : (5202899641 : ℕ)^4389*12500000000000^3365 ≤ 5330971736637^3365*10000000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5202899641 10000000000 5330971736637 12500000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (545668731/1000000000 : ℝ)^4389 ≤ (45381014307147/100000000000000 : ℝ)^3365 := by
    have hnat : (545668731 : ℕ)^4389*100000000000000^3365 ≤ 45381014307147^3365*1000000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      545668731 1000000000 45381014307147 100000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4389/1024 : ℝ)) 4389 3365 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-12277169/62500000 : ℝ), (5202899641/10000000000 : ℝ), (545668731/1000000000 : ℝ)] ![(11971211781801/100000000000000 : ℝ), (5330971736637/12500000000000 : ℝ), (45381014307147/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-12277169/62500000 : ℝ)|^4389 ≤ (11971211781801/100000000000000 : ℝ)^3365
        have hw : |(-12277169/62500000 : ℝ)|=(12277169/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5202899641/10000000000 : ℝ)|^4389 ≤ (5330971736637/12500000000000 : ℝ)^3365
        have hw : |(5202899641/10000000000 : ℝ)|=(5202899641/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(545668731/1000000000 : ℝ)|^4389 ≤ (45381014307147/100000000000000 : ℝ)^3365
        have hw : |(545668731/1000000000 : ℝ)|=(545668731/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1429_s2_5 (p : ℝ) (hpa : (1097/256 : ℝ) ≤ p) (hpb : p ≤ (4389/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1058675851/2000000000 : ℝ)*x 0 + (-1841134719/10000000000 : ℝ)*x 1 + (5456687737/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1058675851/2000000000 : ℝ)^4389 ≤ (43617669981513/100000000000000 : ℝ)^3365 := by
    have hnat : (1058675851 : ℕ)^4389*100000000000000^3365 ≤ 43617669981513^3365*2000000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1058675851 2000000000 43617669981513 100000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1841134719/10000000000 : ℝ)^4389 ≤ (11001311069421/100000000000000 : ℝ)^3365 := by
    have hnat : (1841134719 : ℕ)^4389*100000000000000^3365 ≤ 11001311069421^3365*10000000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1841134719 10000000000 11001311069421 100000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5456687737/10000000000 : ℝ)^4389 ≤ (45381018938987/100000000000000 : ℝ)^3365 := by
    have hnat : (5456687737 : ℕ)^4389*100000000000000^3365 ≤ 45381018938987^3365*10000000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5456687737 10000000000 45381018938987 100000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4389/1024 : ℝ)) 4389 3365 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1058675851/2000000000 : ℝ), (-1841134719/10000000000 : ℝ), (5456687737/10000000000 : ℝ)] ![(43617669981513/100000000000000 : ℝ), (11001311069421/100000000000000 : ℝ), (45381018938987/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1058675851/2000000000 : ℝ)|^4389 ≤ (43617669981513/100000000000000 : ℝ)^3365
        have hw : |(1058675851/2000000000 : ℝ)|=(1058675851/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1841134719/10000000000 : ℝ)|^4389 ≤ (11001311069421/100000000000000 : ℝ)^3365
        have hw : |(-1841134719/10000000000 : ℝ)|=(1841134719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5456687737/10000000000 : ℝ)|^4389 ≤ (45381018938987/100000000000000 : ℝ)^3365
        have hw : |(5456687737/10000000000 : ℝ)|=(5456687737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1429_s2_6 (p : ℝ) (hpa : (1097/256 : ℝ) ≤ p) (hpb : p ≤ (4389/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5293379151/10000000000 : ℝ)*x 0 + (5456687707/10000000000 : ℝ)*x 1 + (-230141863/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5293379151/10000000000 : ℝ)^4389 ≤ (43617668863767/100000000000000 : ℝ)^3365 := by
    have hnat : (5293379151 : ℕ)^4389*100000000000000^3365 ≤ 43617668863767^3365*10000000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5293379151 10000000000 43617668863767 100000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5456687707/10000000000 : ℝ)^4389 ≤ (9076203722713/20000000000000 : ℝ)^3365 := by
    have hnat : (5456687707 : ℕ)^4389*20000000000000^3365 ≤ 9076203722713^3365*10000000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5456687707 10000000000 9076203722713 20000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (230141863/1250000000 : ℝ)^4389 ≤ (11001312511241/100000000000000 : ℝ)^3365 := by
    have hnat : (230141863 : ℕ)^4389*100000000000000^3365 ≤ 11001312511241^3365*1250000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      230141863 1250000000 11001312511241 100000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4389/1024 : ℝ)) 4389 3365 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5293379151/10000000000 : ℝ), (5456687707/10000000000 : ℝ), (-230141863/1250000000 : ℝ)] ![(43617668863767/100000000000000 : ℝ), (9076203722713/20000000000000 : ℝ), (11001312511241/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5293379151/10000000000 : ℝ)|^4389 ≤ (43617668863767/100000000000000 : ℝ)^3365
        have hw : |(5293379151/10000000000 : ℝ)|=(5293379151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5456687707/10000000000 : ℝ)|^4389 ≤ (9076203722713/20000000000000 : ℝ)^3365
        have hw : |(5456687707/10000000000 : ℝ)|=(5456687707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-230141863/1250000000 : ℝ)|^4389 ≤ (11001312511241/100000000000000 : ℝ)^3365
        have hw : |(-230141863/1250000000 : ℝ)|=(230141863/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1429_s2_7 (p : ℝ) (hpa : (1097/256 : ℝ) ≤ p) (hpb : p ≤ (4389/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (860025171/2000000000 : ℝ)*x 0 + (4582604409/10000000000 : ℝ)*x 1 + (4033575999/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (860025171/2000000000 : ℝ)^4389 ≤ (8315457958171/25000000000000 : ℝ)^3365 := by
    have hnat : (860025171 : ℕ)^4389*25000000000000^3365 ≤ 8315457958171^3365*2000000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      860025171 2000000000 8315457958171 25000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4582604409/10000000000 : ℝ)^4389 ≤ (7227960764277/20000000000000 : ℝ)^3365 := by
    have hnat : (4582604409 : ℕ)^4389*20000000000000^3365 ≤ 7227960764277^3365*10000000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4582604409 10000000000 7227960764277 20000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4033575999/10000000000 : ℝ)^4389 ≤ (15299182167457/50000000000000 : ℝ)^3365 := by
    have hnat : (4033575999 : ℕ)^4389*50000000000000^3365 ≤ 15299182167457^3365*10000000000^4389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4033575999 10000000000 15299182167457 50000000000000 4389 3365 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4389/1024 : ℝ)) 4389 3365 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(860025171/2000000000 : ℝ), (4582604409/10000000000 : ℝ), (4033575999/10000000000 : ℝ)] ![(8315457958171/25000000000000 : ℝ), (7227960764277/20000000000000 : ℝ), (15299182167457/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(860025171/2000000000 : ℝ)|^4389 ≤ (8315457958171/25000000000000 : ℝ)^3365
        have hw : |(860025171/2000000000 : ℝ)|=(860025171/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4582604409/10000000000 : ℝ)|^4389 ≤ (7227960764277/20000000000000 : ℝ)^3365
        have hw : |(4582604409/10000000000 : ℝ)|=(4582604409/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4033575999/10000000000 : ℝ)|^4389 ≤ (15299182167457/50000000000000 : ℝ)^3365
        have hw : |(4033575999/10000000000 : ℝ)|=(4033575999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1429_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1097/256 : ℝ) ≤ p) (hpb : p ≤ (4389/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158166723/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9423/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1913/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (324/3125 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15799/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (9423/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1913/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (9423/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1913/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (9423/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1913/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (9423/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1913/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (9423/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1913/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (9423/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1913/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
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
  have hpowlo : (1913/25000 : ℝ) ^ (1097/256 : ℝ) ≤ (164740848785211/10000000000000000000 : ℝ) := by
    have hpowers : (1913/25000 : ℝ)^1097 ≤ (164740848785211/10000000000000000000 : ℝ)^256 := by
      have hnat : (1913 : ℕ)^1097*10000000000000000000^256 ≤ 164740848785211^256*25000^1097 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1913 25000 164740848785211 10000000000000000000 1097 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1913/25000 : ℝ)) (X := (164740848785211/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1097 256 (by norm_num) hpowers
    exact h
  have hpowhi : (9423/50000 : ℝ) ^ (1097/256 : ℝ) ≤ (78379225617878583/100000000000000000000 : ℝ) := by
    have hpowers : (9423/50000 : ℝ)^1097 ≤ (78379225617878583/100000000000000000000 : ℝ)^256 := by
      have hnat : (9423 : ℕ)^1097*100000000000000000000^256 ≤ 78379225617878583^256*50000^1097 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9423 50000 78379225617878583 100000000000000000000 1097 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9423/50000 : ℝ)) (X := (78379225617878583/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1097 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (5000164740848785211/5000000000000000000 : ℝ) ≤ (10000076888103303/10000000000000000 : ℝ) ^ (1097/256 : ℝ) := by
    have hpowers : (5000164740848785211/5000000000000000000 : ℝ)^256 ≤ (10000076888103303/10000000000000000 : ℝ)^1097 := by
      have hnat : (5000164740848785211 : ℕ)^256*10000000000000000^1097 ≤ 10000076888103303^1097*5000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5000164740848785211 5000000000000000000 10000076888103303 10000000000000000 256 1097 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000076888103303/10000000000000000 : ℝ)) (X := (5000164740848785211/5000000000000000000 : ℝ)) (by norm_num) 1097 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (100080026634105730693/100000000000000000000 : ℝ) ≤ (2000373391737907/2000000000000000 : ℝ) ^ (1097/256 : ℝ) := by
    have hpowers : (100080026634105730693/100000000000000000000 : ℝ)^256 ≤ (2000373391737907/2000000000000000 : ℝ)^1097 := by
      have hnat : (100080026634105730693 : ℕ)^256*2000000000000000^1097 ≤ 2000373391737907^1097*100000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100080026634105730693 100000000000000000000 2000373391737907 2000000000000000 256 1097 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000373391737907/2000000000000000 : ℝ)) (X := (100080026634105730693/100000000000000000000 : ℝ)) (by norm_num) 1097 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (50078379225617878583/50000000000000000000 : ℝ) ≤ (10003657029275767/10000000000000000 : ℝ) ^ (1097/256 : ℝ) := by
    have hpowers : (50078379225617878583/50000000000000000000 : ℝ)^256 ≤ (10003657029275767/10000000000000000 : ℝ)^1097 := by
      have hnat : (50078379225617878583 : ℕ)^256*10000000000000000^1097 ≤ 10003657029275767^1097*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50078379225617878583 50000000000000000000 10003657029275767 10000000000000000 256 1097 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003657029275767/10000000000000000 : ℝ)) (X := (50078379225617878583/50000000000000000000 : ℝ)) (by norm_num) 1097 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(164740848785211/10000000000000000000 : ℝ) ≤ ((55956732722588339627/55970000000000000000 : ℝ)+2*(223758823279/139925000000000 : ℝ)*(1913/25000 : ℝ))^(1097/256 : ℝ) := by
    rw [show (55956732722588339627/55970000000000000000 : ℝ)+2*(223758823279/139925000000000 : ℝ)*(1913/25000 : ℝ)=(10000076888103303/10000000000000000 : ℝ) by norm_num, show 1+2*(164740848785211/10000000000000000000 : ℝ)=(5000164740848785211/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(78379225617878583/100000000000000000000 : ℝ)+(164740848785211/10000000000000000000 : ℝ) ≤ ((55956732722588339627/55970000000000000000 : ℝ)+(223758823279/139925000000000 : ℝ)*((9423/50000 : ℝ)+(1913/25000 : ℝ)))^(1097/256 : ℝ) := by
    rw [show (55956732722588339627/55970000000000000000 : ℝ)+(223758823279/139925000000000 : ℝ)*((9423/50000 : ℝ)+(1913/25000 : ℝ))=(2000373391737907/2000000000000000 : ℝ) by norm_num, show 1+(78379225617878583/100000000000000000000 : ℝ)+(164740848785211/10000000000000000000 : ℝ)=(100080026634105730693/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(78379225617878583/100000000000000000000 : ℝ) ≤ ((55956732722588339627/55970000000000000000 : ℝ)+2*(223758823279/139925000000000 : ℝ)*(9423/50000 : ℝ))^(1097/256 : ℝ) := by
    rw [show (55956732722588339627/55970000000000000000 : ℝ)+2*(223758823279/139925000000000 : ℝ)*(9423/50000 : ℝ)=(10003657029275767/10000000000000000 : ℝ) by norm_num, show 1+2*(78379225617878583/100000000000000000000 : ℝ)=(50078379225617878583/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (55956732722588339627/55970000000000000000 : ℝ)*(X 1 0+X 2 0)+(223758823279/139925000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1097/256 : ℝ)) (lo := (1913/25000 : ℝ)) (hi := (9423/50000 : ℝ)) (c := (55956732722588339627/55970000000000000000 : ℝ)) (alpha := (223758823279/139925000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (55956732722588339627/55970000000000000000 : ℝ)*(X 0 1+X 2 1)+(223758823279/139925000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1097/256 : ℝ)) (lo := (1913/25000 : ℝ)) (hi := (9423/50000 : ℝ)) (c := (55956732722588339627/55970000000000000000 : ℝ)) (alpha := (223758823279/139925000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (55956732722588339627/55970000000000000000 : ℝ)*(X 0 2+X 1 2)+(223758823279/139925000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1097/256 : ℝ)) (lo := (1913/25000 : ℝ)) (hi := (9423/50000 : ℝ)) (c := (55956732722588339627/55970000000000000000 : ℝ)) (alpha := (223758823279/139925000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-245537683/1250000000 : ℝ)*X 0 0+(1364542033/2500000000 : ℝ)*X 0 1+(2600715481/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1429_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5360139499/10000000000 : ℝ)*X 1 0+(-2096391443/10000000000 : ℝ)*X 1 1+(2600715429/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1429_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2680069559/5000000000 : ℝ)*X 2 0+(5201431291/10000000000 : ℝ)*X 2 1+(-104819569/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1429_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2150013723/5000000000 : ℝ)*X 0 0+(2015186429/5000000000 : ℝ)*X 0 1+(1146445339/2500000000 : ℝ)*X 0 2+(2150013723/5000000000 : ℝ)*X 1 0+(2015186429/5000000000 : ℝ)*X 1 1+(1146445339/2500000000 : ℝ)*X 1 2+(2150013723/5000000000 : ℝ)*X 2 0+(2015186429/5000000000 : ℝ)*X 2 1+(1146445339/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1429_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-12277169/62500000 : ℝ)*X 0 0+(5202899641/10000000000 : ℝ)*X 0 1+(545668731/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1429_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1058675851/2000000000 : ℝ)*X 1 0+(-1841134719/10000000000 : ℝ)*X 1 1+(5456687737/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1429_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5293379151/10000000000 : ℝ)*X 2 0+(5456687707/10000000000 : ℝ)*X 2 1+(-230141863/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1429_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((860025171/2000000000 : ℝ)*X 0 0+(4582604409/10000000000 : ℝ)*X 0 1+(4033575999/10000000000 : ℝ)*X 0 2+(860025171/2000000000 : ℝ)*X 1 0+(4582604409/10000000000 : ℝ)*X 1 1+(4033575999/10000000000 : ℝ)*X 1 2+(860025171/2000000000 : ℝ)*X 2 0+(4582604409/10000000000 : ℝ)*X 2 1+(4033575999/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1429_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4946266267430066361682833483/1399250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2490397/4000000000000 : ℝ)*(base19) + (196421/25000000000000 : ℝ)*(lower2) + (31924187/100000000000000 : ℝ)*(upper3) + (25511583/25000000000000 : ℝ)*(lower4) + (15560843/20000000000000 : ℝ)*(upper5) + (1423878651753643/50000000000000 : ℝ)*(major0) + (1423878651753643/50000000000000 : ℝ)*(major1) + (1423878651753643/50000000000000 : ℝ)*(major2) + (1947517967196809/50000000000000 : ℝ)*(sp0) + (973758551230861/25000000000000 : ℝ)*(sp1) + (1947518164748207/50000000000000 : ℝ)*(sp2) + (90023907984339/5000000000000 : ℝ)*(sp3) + (79020559/20000000000000 : ℝ)*(sp4) + (412462609/20000000000000 : ℝ)*(sp5) + (90023907984339/5000000000000 : ℝ)*(f.failure) + (1947518164748207/50000000000000 : ℝ)*(f.sum) + (7978387400881/1749062500000000000000000000 : ℝ)*base65 + (5012425771693811161/2798500000000000000000000000000000 : ℝ)*base67 + (5241594279046311161/2798500000000000000000000000000000 : ℝ)*base69 + (16514656281556188839/2798500000000000000000000000000000 : ℝ)*base72 + (32025073487929/27985000000000000000000000000 : ℝ)*base74 + (13434005595527188839/2798500000000000000000000000000000 : ℝ)*base76 + (138942669790124688839/2798500000000000000000000000000000 : ℝ)*base78 + (9753893908251688839/2798500000000000000000000000000000 : ℝ)*base80 + (4883224812589/1749062500000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (4951097/500000000000000000000 : ℝ)*base89 + (4951097/500000000000000000000 : ℝ)*base91 + (4951097/500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4598313569392913995500606171/1399250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1244167/4000000000000 : ℝ)*(base15) + (1487833/20000000000000 : ℝ)*(lower2) + (29656269/25000000000000 : ℝ)*(upper3) + (60608511/100000000000000 : ℝ)*(lower4) + (2880848678501909/100000000000000 : ℝ)*(major0) + (2880848678501909/100000000000000 : ℝ)*(major1) + (2880848678501909/100000000000000 : ℝ)*(major2) + (1279222729/100000000000000 : ℝ)*(sp1) + (1646109733/100000000000000 : ℝ)*(sp2) + (31381691/100000000000000 : ℝ)*(sp3) + (1970148628226021/50000000000000 : ℝ)*(sp4) + (1970147973062569/50000000000000 : ℝ)*(sp5) + (394029561034231/10000000000000 : ℝ)*(sp6) + (910699979813869/50000000000000 : ℝ)*(sp7) + (1821399991009429/100000000000000 : ℝ)*(f.failure) + (1970148628226021/50000000000000 : ℝ)*(f.sum) + (40201532923221/6996250000000000000000000000 : ℝ)*base65 + (4056978284630247943/5597000000000000000000000000000000 : ℝ)*base67 + (18523859653938247943/5597000000000000000000000000000000 : ℝ)*base69 + (54880058269115247943/5597000000000000000000000000000000 : ℝ)*base71 + (23857481886291/27985000000000000000000000000 : ℝ)*base74 + (36083791364642247943/5597000000000000000000000000000000 : ℝ)*base75 + (25516352936344247943/5597000000000000000000000000000000 : ℝ)*base77 + (20733934436316752057/5597000000000000000000000000000000 : ℝ)*base80 + (3671177986693/13992500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (52968833/10000000000000000000000 : ℝ)*base90 + (52968833/10000000000000000000000 : ℝ)*base92 + (52968833/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1429_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1097/256 : ℝ) ≤ p) (hpb : p ≤ (4389/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158166723/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9423/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1913/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (324/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15799/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1429_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1429_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1097/256 : ℝ) ≤ p) (hpb : p ≤ (4389/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158166723/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (324/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15799/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1429_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1429_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1429_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (1097/256 : ℝ) ≤ p) (hpb : p ≤ (4389/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158166723/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (324/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15799/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1429_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
