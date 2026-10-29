-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1439_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:56:37.317112+00:00
-- url     : https://prove2.me/submissions/fb30463c-5650-41f3-9140-44450af951e9

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
theorem support_rectangle_w1439_s0_0 (p : ℝ) (hpa : (2199/512 : ℝ) ≤ p) (hpb : p ≤ (4399/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1753166079/10000000000 : ℝ)*x 0 + (2978032599/5000000000 : ℝ)*x 1 + (2416759749/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1753166079/10000000000 : ℝ)^4399 ≤ (5168486405743/50000000000000 : ℝ)^3375 := by
    have hnat : (1753166079 : ℕ)^4399*50000000000000^3375 ≤ 5168486405743^3375*10000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1753166079 10000000000 5168486405743 50000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2978032599/5000000000 : ℝ)^4399 ≤ (25447813630457/50000000000000 : ℝ)^3375 := by
    have hnat : (2978032599 : ℕ)^4399*50000000000000^3375 ≤ 25447813630457^3375*5000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2978032599 5000000000 25447813630457 50000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2416759749/5000000000 : ℝ)^4399 ≤ (9691849977951/25000000000000 : ℝ)^3375 := by
    have hnat : (2416759749 : ℕ)^4399*25000000000000^3375 ≤ 9691849977951^3375*5000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2416759749 5000000000 9691849977951 25000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4399/1024 : ℝ)) 4399 3375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1753166079/10000000000 : ℝ), (2978032599/5000000000 : ℝ), (2416759749/5000000000 : ℝ)] ![(5168486405743/50000000000000 : ℝ), (25447813630457/50000000000000 : ℝ), (9691849977951/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1753166079/10000000000 : ℝ)|^4399 ≤ (5168486405743/50000000000000 : ℝ)^3375
        have hw : |(-1753166079/10000000000 : ℝ)|=(1753166079/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2978032599/5000000000 : ℝ)|^4399 ≤ (25447813630457/50000000000000 : ℝ)^3375
        have hw : |(2978032599/5000000000 : ℝ)|=(2978032599/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2416759749/5000000000 : ℝ)|^4399 ≤ (9691849977951/25000000000000 : ℝ)^3375
        have hw : |(2416759749/5000000000 : ℝ)|=(2416759749/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1439_s0_1 (p : ℝ) (hpa : (2199/512 : ℝ) ≤ p) (hpb : p ≤ (4399/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5490987667/10000000000 : ℝ)*x 0 + (-1193425191/5000000000 : ℝ)*x 1 + (4833519673/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5490987667/10000000000 : ℝ)^4399 ≤ (22889088385007/50000000000000 : ℝ)^3375 := by
    have hnat : (5490987667 : ℕ)^4399*50000000000000^3375 ≤ 22889088385007^3375*10000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5490987667 10000000000 22889088385007 50000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1193425191/5000000000 : ℝ)^4399 ≤ (3863605369717/25000000000000 : ℝ)^3375 := by
    have hnat : (1193425191 : ℕ)^4399*25000000000000^3375 ≤ 3863605369717^3375*5000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1193425191 5000000000 3863605369717 25000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4833519673/10000000000 : ℝ)^4399 ≤ (19383700870629/50000000000000 : ℝ)^3375 := by
    have hnat : (4833519673 : ℕ)^4399*50000000000000^3375 ≤ 19383700870629^3375*10000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4833519673 10000000000 19383700870629 50000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4399/1024 : ℝ)) 4399 3375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5490987667/10000000000 : ℝ), (-1193425191/5000000000 : ℝ), (4833519673/10000000000 : ℝ)] ![(22889088385007/50000000000000 : ℝ), (3863605369717/25000000000000 : ℝ), (19383700870629/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5490987667/10000000000 : ℝ)|^4399 ≤ (22889088385007/50000000000000 : ℝ)^3375
        have hw : |(5490987667/10000000000 : ℝ)|=(5490987667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1193425191/5000000000 : ℝ)|^4399 ≤ (3863605369717/25000000000000 : ℝ)^3375
        have hw : |(-1193425191/5000000000 : ℝ)|=(1193425191/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4833519673/10000000000 : ℝ)|^4399 ≤ (19383700870629/50000000000000 : ℝ)^3375
        have hw : |(4833519673/10000000000 : ℝ)|=(4833519673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1439_s0_2 (p : ℝ) (hpa : (2199/512 : ℝ) ≤ p) (hpb : p ≤ (4399/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2745493899/5000000000 : ℝ)*x 0 + (193340787/400000000 : ℝ)*x 1 + (-238685021/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2745493899/5000000000 : ℝ)^4399 ≤ (572227227419/1250000000000 : ℝ)^3375 := by
    have hnat : (2745493899 : ℕ)^4399*1250000000000^3375 ≤ 572227227419^3375*5000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2745493899 5000000000 572227227419 1250000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (193340787/400000000 : ℝ)^4399 ≤ (19383700881083/50000000000000 : ℝ)^3375 := by
    have hnat : (193340787 : ℕ)^4399*50000000000000^3375 ≤ 19383700881083^3375*400000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      193340787 400000000 19383700881083 50000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (238685021/1000000000 : ℝ)^4399 ≤ (1931802503413/12500000000000 : ℝ)^3375 := by
    have hnat : (238685021 : ℕ)^4399*12500000000000^3375 ≤ 1931802503413^3375*1000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      238685021 1000000000 1931802503413 12500000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4399/1024 : ℝ)) 4399 3375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2745493899/5000000000 : ℝ), (193340787/400000000 : ℝ), (-238685021/1000000000 : ℝ)] ![(572227227419/1250000000000 : ℝ), (19383700881083/50000000000000 : ℝ), (1931802503413/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2745493899/5000000000 : ℝ)|^4399 ≤ (572227227419/1250000000000 : ℝ)^3375
        have hw : |(2745493899/5000000000 : ℝ)|=(2745493899/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(193340787/400000000 : ℝ)|^4399 ≤ (19383700881083/50000000000000 : ℝ)^3375
        have hw : |(193340787/400000000 : ℝ)|=(193340787/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-238685021/1000000000 : ℝ)|^4399 ≤ (1931802503413/12500000000000 : ℝ)^3375
        have hw : |(-238685021/1000000000 : ℝ)|=(238685021/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1439_s0_3 (p : ℝ) (hpa : (2199/512 : ℝ) ≤ p) (hpb : p ≤ (4399/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4164569771/10000000000 : ℝ)*x 0 + (3103123973/10000000000 : ℝ)*x 1 + (5540465551/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4164569771/10000000000 : ℝ)^4399 ≤ (15963014567409/50000000000000 : ℝ)^3375 := by
    have hnat : (4164569771 : ℕ)^4399*50000000000000^3375 ≤ 15963014567409^3375*10000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4164569771 10000000000 15963014567409 50000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3103123973/10000000000 : ℝ)^4399 ≤ (10878705531671/50000000000000 : ℝ)^3375 := by
    have hnat : (3103123973 : ℕ)^4399*50000000000000^3375 ≤ 10878705531671^3375*10000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3103123973 10000000000 10878705531671 50000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5540465551/10000000000 : ℝ)^4399 ≤ (144739249327/312500000000 : ℝ)^3375 := by
    have hnat : (5540465551 : ℕ)^4399*312500000000^3375 ≤ 144739249327^3375*10000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5540465551 10000000000 144739249327 312500000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4399/1024 : ℝ)) 4399 3375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4164569771/10000000000 : ℝ), (3103123973/10000000000 : ℝ), (5540465551/10000000000 : ℝ)] ![(15963014567409/50000000000000 : ℝ), (10878705531671/50000000000000 : ℝ), (144739249327/312500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4164569771/10000000000 : ℝ)|^4399 ≤ (15963014567409/50000000000000 : ℝ)^3375
        have hw : |(4164569771/10000000000 : ℝ)|=(4164569771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3103123973/10000000000 : ℝ)|^4399 ≤ (10878705531671/50000000000000 : ℝ)^3375
        have hw : |(3103123973/10000000000 : ℝ)|=(3103123973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5540465551/10000000000 : ℝ)|^4399 ≤ (144739249327/312500000000 : ℝ)^3375
        have hw : |(5540465551/10000000000 : ℝ)|=(5540465551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1439_s0_4 (p : ℝ) (hpa : (2199/512 : ℝ) ≤ p) (hpb : p ≤ (4399/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1757135371/10000000000 : ℝ)*x 0 + (243110933/500000000 : ℝ)*x 1 + (370396347/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1757135371/10000000000 : ℝ)^4399 ≤ (10367487757839/100000000000000 : ℝ)^3375 := by
    have hnat : (1757135371 : ℕ)^4399*100000000000000^3375 ≤ 10367487757839^3375*10000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1757135371 10000000000 10367487757839 100000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (243110933/500000000 : ℝ)^4399 ≤ (4883461429571/12500000000000 : ℝ)^3375 := by
    have hnat : (243110933 : ℕ)^4399*12500000000000^3375 ≤ 4883461429571^3375*500000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      243110933 500000000 4883461429571 12500000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (370396347/625000000 : ℝ)^4399 ≤ (50564820792313/100000000000000 : ℝ)^3375 := by
    have hnat : (370396347 : ℕ)^4399*100000000000000^3375 ≤ 50564820792313^3375*625000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      370396347 625000000 50564820792313 100000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4399/1024 : ℝ)) 4399 3375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1757135371/10000000000 : ℝ), (243110933/500000000 : ℝ), (370396347/625000000 : ℝ)] ![(10367487757839/100000000000000 : ℝ), (4883461429571/12500000000000 : ℝ), (50564820792313/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1757135371/10000000000 : ℝ)|^4399 ≤ (10367487757839/100000000000000 : ℝ)^3375
        have hw : |(-1757135371/10000000000 : ℝ)|=(1757135371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(243110933/500000000 : ℝ)|^4399 ≤ (4883461429571/12500000000000 : ℝ)^3375
        have hw : |(243110933/500000000 : ℝ)|=(243110933/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(370396347/625000000 : ℝ)|^4399 ≤ (50564820792313/100000000000000 : ℝ)^3375
        have hw : |(370396347/625000000 : ℝ)|=(370396347/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1439_s0_5 (p : ℝ) (hpa : (2199/512 : ℝ) ≤ p) (hpb : p ≤ (4399/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5184556259/10000000000 : ℝ)*x 0 + (-129402803/1000000000 : ℝ)*x 1 + (2963170811/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5184556259/10000000000 : ℝ)^4399 ≤ (42476915750853/100000000000000 : ℝ)^3375 := by
    have hnat : (5184556259 : ℕ)^4399*100000000000000^3375 ≤ 42476915750853^3375*10000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5184556259 10000000000 42476915750853 100000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (129402803/1000000000 : ℝ)^4399 ≤ (6958262671391/100000000000000 : ℝ)^3375 := by
    have hnat : (129402803 : ℕ)^4399*100000000000000^3375 ≤ 6958262671391^3375*1000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      129402803 1000000000 6958262671391 100000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2963170811/5000000000 : ℝ)^4399 ≤ (2528241078539/5000000000000 : ℝ)^3375 := by
    have hnat : (2963170811 : ℕ)^4399*5000000000000^3375 ≤ 2528241078539^3375*5000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2963170811 5000000000 2528241078539 5000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4399/1024 : ℝ)) 4399 3375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5184556259/10000000000 : ℝ), (-129402803/1000000000 : ℝ), (2963170811/5000000000 : ℝ)] ![(42476915750853/100000000000000 : ℝ), (6958262671391/100000000000000 : ℝ), (2528241078539/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5184556259/10000000000 : ℝ)|^4399 ≤ (42476915750853/100000000000000 : ℝ)^3375
        have hw : |(5184556259/10000000000 : ℝ)|=(5184556259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-129402803/1000000000 : ℝ)|^4399 ≤ (6958262671391/100000000000000 : ℝ)^3375
        have hw : |(-129402803/1000000000 : ℝ)|=(129402803/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2963170811/5000000000 : ℝ)|^4399 ≤ (2528241078539/5000000000000 : ℝ)^3375
        have hw : |(2963170811/5000000000 : ℝ)|=(2963170811/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1439_s0_6 (p : ℝ) (hpa : (2199/512 : ℝ) ≤ p) (hpb : p ≤ (4399/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1036911257/2000000000 : ℝ)*x 0 + (2963170733/5000000000 : ℝ)*x 1 + (-1294028237/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1036911257/2000000000 : ℝ)^4399 ≤ (42476916028501/100000000000000 : ℝ)^3375 := by
    have hnat : (1036911257 : ℕ)^4399*100000000000000^3375 ≤ 42476916028501^3375*2000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1036911257 2000000000 42476916028501 100000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2963170733/5000000000 : ℝ)^4399 ≤ (50564819835911/100000000000000 : ℝ)^3375 := by
    have hnat : (2963170733 : ℕ)^4399*100000000000000^3375 ≤ 50564819835911^3375*5000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2963170733 5000000000 50564819835911 100000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1294028237/10000000000 : ℝ)^4399 ≤ (6958264122191/100000000000000 : ℝ)^3375 := by
    have hnat : (1294028237 : ℕ)^4399*100000000000000^3375 ≤ 6958264122191^3375*10000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1294028237 10000000000 6958264122191 100000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4399/1024 : ℝ)) 4399 3375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1036911257/2000000000 : ℝ), (2963170733/5000000000 : ℝ), (-1294028237/10000000000 : ℝ)] ![(42476916028501/100000000000000 : ℝ), (50564819835911/100000000000000 : ℝ), (6958264122191/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1036911257/2000000000 : ℝ)|^4399 ≤ (42476916028501/100000000000000 : ℝ)^3375
        have hw : |(1036911257/2000000000 : ℝ)|=(1036911257/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2963170733/5000000000 : ℝ)|^4399 ≤ (50564819835911/100000000000000 : ℝ)^3375
        have hw : |(2963170733/5000000000 : ℝ)|=(2963170733/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1294028237/10000000000 : ℝ)|^4399 ≤ (6958264122191/100000000000000 : ℝ)^3375
        have hw : |(-1294028237/10000000000 : ℝ)|=(1294028237/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1439_s0_7 (p : ℝ) (hpa : (2199/512 : ℝ) ≤ p) (hpb : p ≤ (4399/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2086594873/5000000000 : ℝ)*x 0 + (2739076217/5000000000 : ℝ)*x 1 + (126706471/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2086594873/5000000000 : ℝ)^4399 ≤ (32012187457709/100000000000000 : ℝ)^3375 := by
    have hnat : (2086594873 : ℕ)^4399*100000000000000^3375 ≤ 32012187457709^3375*5000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2086594873 5000000000 32012187457709 100000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2739076217/5000000000 : ℝ)^4399 ≤ (5704844083757/12500000000000 : ℝ)^3375 := by
    have hnat : (2739076217 : ℕ)^4399*12500000000000^3375 ≤ 5704844083757^3375*5000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2739076217 5000000000 5704844083757 12500000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (126706471/400000000 : ℝ)^4399 ≤ (5587264965249/25000000000000 : ℝ)^3375 := by
    have hnat : (126706471 : ℕ)^4399*25000000000000^3375 ≤ 5587264965249^3375*400000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      126706471 400000000 5587264965249 25000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4399/1024 : ℝ)) 4399 3375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2086594873/5000000000 : ℝ), (2739076217/5000000000 : ℝ), (126706471/400000000 : ℝ)] ![(32012187457709/100000000000000 : ℝ), (5704844083757/12500000000000 : ℝ), (5587264965249/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2086594873/5000000000 : ℝ)|^4399 ≤ (32012187457709/100000000000000 : ℝ)^3375
        have hw : |(2086594873/5000000000 : ℝ)|=(2086594873/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2739076217/5000000000 : ℝ)|^4399 ≤ (5704844083757/12500000000000 : ℝ)^3375
        have hw : |(2739076217/5000000000 : ℝ)|=(2739076217/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(126706471/400000000 : ℝ)|^4399 ≤ (5587264965249/25000000000000 : ℝ)^3375
        have hw : |(126706471/400000000 : ℝ)|=(126706471/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1439_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2199/512 : ℝ) ≤ p) (hpb : p ≤ (4399/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158563157/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (1059/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (26189/100000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (2199/512 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^2199 ≤ (0 : ℝ)^512 := by
      have hnat : (0 : ℕ)^2199*1^512 ≤ 0^512*1^2199 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 2199 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 2199 512 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (2199/512 : ℝ) ≤ (488448477779851487/25000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^2199 ≤ (488448477779851487/25000000000000000000 : ℝ)^512 := by
      have hnat : (2 : ℕ)^2199*25000000000000000000^512 ≤ 488448477779851487^512*5^2199 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 488448477779851487 25000000000000000000 2199 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (488448477779851487/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2199 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (2199/512 : ℝ) := by
    have hpowers : (1 : ℝ)^512 ≤ (1 : ℝ)^2199 := by
      have hnat : (1 : ℕ)^512*1^2199 ≤ 1^2199*1^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 512 2199 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 2199 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (25488448477779851487/25000000000000000000 : ℝ) ≤ (10045153734373779/10000000000000000 : ℝ) ^ (2199/512 : ℝ) := by
    have hpowers : (25488448477779851487/25000000000000000000 : ℝ)^512 ≤ (10045153734373779/10000000000000000 : ℝ)^2199 := by
      have hnat : (25488448477779851487 : ℕ)^512*10000000000000000^2199 ≤ 10045153734373779^2199*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25488448477779851487 25000000000000000000 10045153734373779 10000000000000000 512 2199 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10045153734373779/10000000000000000 : ℝ)) (X := (25488448477779851487/25000000000000000000 : ℝ)) (by norm_num) 2199 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (12988448477779851487/12500000000000000000 : ℝ) ≤ (5045153734373779/5000000000000000 : ℝ) ^ (2199/512 : ℝ) := by
    have hpowers : (12988448477779851487/12500000000000000000 : ℝ)^512 ≤ (5045153734373779/5000000000000000 : ℝ)^2199 := by
      have hnat : (12988448477779851487 : ℕ)^512*5000000000000000^2199 ≤ 5045153734373779^2199*12500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12988448477779851487 12500000000000000000 5045153734373779 5000000000000000 512 2199 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5045153734373779/5000000000000000 : ℝ)) (X := (12988448477779851487/12500000000000000000 : ℝ)) (by norm_num) 2199 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(45153734373779/4000000000000000 : ℝ)*(0 : ℝ))^(2199/512 : ℝ) := by
    rw [show (1 : ℝ)+2*(45153734373779/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(488448477779851487/25000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(45153734373779/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(2199/512 : ℝ) := by
    rw [show (1 : ℝ)+(45153734373779/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10045153734373779/10000000000000000 : ℝ) by norm_num, show 1+(488448477779851487/25000000000000000000 : ℝ)+(0 : ℝ)=(25488448477779851487/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(488448477779851487/25000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(45153734373779/4000000000000000 : ℝ)*(2/5 : ℝ))^(2199/512 : ℝ) := by
    rw [show (1 : ℝ)+2*(45153734373779/4000000000000000 : ℝ)*(2/5 : ℝ)=(5045153734373779/5000000000000000 : ℝ) by norm_num, show 1+2*(488448477779851487/25000000000000000000 : ℝ)=(12988448477779851487/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(45153734373779/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2199/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (45153734373779/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(45153734373779/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2199/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (45153734373779/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(45153734373779/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2199/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (45153734373779/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1753166079/10000000000 : ℝ)*X 0 0+(2978032599/5000000000 : ℝ)*X 0 1+(2416759749/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1439_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5490987667/10000000000 : ℝ)*X 1 0+(-1193425191/5000000000 : ℝ)*X 1 1+(4833519673/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1439_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2745493899/5000000000 : ℝ)*X 2 0+(193340787/400000000 : ℝ)*X 2 1+(-238685021/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1439_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4164569771/10000000000 : ℝ)*X 0 0+(3103123973/10000000000 : ℝ)*X 0 1+(5540465551/10000000000 : ℝ)*X 0 2+(4164569771/10000000000 : ℝ)*X 1 0+(3103123973/10000000000 : ℝ)*X 1 1+(5540465551/10000000000 : ℝ)*X 1 2+(4164569771/10000000000 : ℝ)*X 2 0+(3103123973/10000000000 : ℝ)*X 2 1+(5540465551/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1439_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1757135371/10000000000 : ℝ)*X 0 0+(243110933/500000000 : ℝ)*X 0 1+(370396347/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1439_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5184556259/10000000000 : ℝ)*X 1 0+(-129402803/1000000000 : ℝ)*X 1 1+(2963170811/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1439_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1036911257/2000000000 : ℝ)*X 2 0+(2963170733/5000000000 : ℝ)*X 2 1+(-1294028237/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1439_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2086594873/5000000000 : ℝ)*X 0 0+(2739076217/5000000000 : ℝ)*X 0 1+(126706471/400000000 : ℝ)*X 0 2+(2086594873/5000000000 : ℝ)*X 1 0+(2739076217/5000000000 : ℝ)*X 1 1+(126706471/400000000 : ℝ)*X 1 2+(2086594873/5000000000 : ℝ)*X 2 0+(2739076217/5000000000 : ℝ)*X 2 1+(126706471/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1439_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (495950350299882220833087/100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (597342109/50000000000000 : ℝ)*(base19) + (1190228473/100000000000000 : ℝ)*(base23) + (147550953/100000000000000 : ℝ)*(upper3) + (14116641/100000000000000 : ℝ)*(upper4) + (177187107/100000000000000 : ℝ)*(upper5) + (650563889314083/100000000000000 : ℝ)*(major0) + (650563889314083/100000000000000 : ℝ)*(major1) + (650563889314083/100000000000000 : ℝ)*(major2) + (222709063795903/25000000000000 : ℝ)*(sp0) + (178167900204229/20000000000000 : ℝ)*(sp1) + (89083950547689/10000000000000 : ℝ)*(sp2) + (41028497789589/10000000000000 : ℝ)*(sp3) + (4440521751/100000000000000 : ℝ)*(sp4) + (969855061/50000000000000 : ℝ)*(sp7) + (410286917606013/100000000000000 : ℝ)*(f.failure) + (890840695705363/100000000000000 : ℝ)*(f.sum) + (1232240204029657/200000000000000000000000000000 : ℝ)*base65 + (3935373149029657/400000000000000000000000000000 : ℝ)*base67 + (1173165343429657/400000000000000000000000000000 : ℝ)*base69 + (5016952283829657/400000000000000000000000000000 : ℝ)*base71 + (1043703745029657/200000000000000000000000000000 : ℝ)*base73 + (1067836840629657/400000000000000000000000000000 : ℝ)*base75 + (2593044481829657/400000000000000000000000000000 : ℝ)*base77 + (3258732383429657/400000000000000000000000000000 : ℝ)*base79 + (265654842629657/200000000000000000000000000000 : ℝ)*base81 + (3463041/10000000000000000000000 : ℝ)*base89 + (3463041/10000000000000000000000 : ℝ)*base91 + (3463041/10000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (24031647559359704463813/6250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (438755497/50000000000000 : ℝ)*(base19) + (884750337/100000000000000 : ℝ)*(base23) + (55468653/50000000000000 : ℝ)*(base32) + (135780837/100000000000000 : ℝ)*(upper3) + (69831209/100000000000000 : ℝ)*(upper5) + (85784316485301/12500000000000 : ℝ)*(major0) + (85784316485301/12500000000000 : ℝ)*(major1) + (85784316485301/12500000000000 : ℝ)*(major2) + (2088769801/100000000000000 : ℝ)*(sp1) + (532879449/25000000000000 : ℝ)*(sp2) + (469870309080861/50000000000000 : ℝ)*(sp4) + (939737651880927/100000000000000 : ℝ)*(sp5) + (234934400473397/25000000000000 : ℝ)*(sp6) + (216404103248497/50000000000000 : ℝ)*(sp7) + (4328083174343/1000000000000 : ℝ)*(f.failure) + (469870309080861/50000000000000 : ℝ)*(f.sum) + (8108373227521/25000000000000000000000000000 : ℝ)*base66 + (277249697522479/50000000000000000000000000000 : ℝ)*base67 + (97761648622479/50000000000000000000000000000 : ℝ)*base69 + (190583499122479/50000000000000000000000000000 : ℝ)*base71 + (144608353222479/25000000000000000000000000000 : ℝ)*base73 + (56493342472479/50000000000000000000000000000 : ℝ)*base75 + (244141627722479/50000000000000000000000000000 : ℝ)*base77 + (494428508122479/50000000000000000000000000000 : ℝ)*base79 + (22204922472479/25000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (519149/100000000000000000000 : ℝ)*base90 + (519149/100000000000000000000 : ℝ)*base92 + (519149/100000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1439_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2199/512 : ℝ) ≤ p) (hpb : p ≤ (4399/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158563157/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1059/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (26189/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1439_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1439_s1_0 (p : ℝ) (hpa : (2199/512 : ℝ) ≤ p) (hpb : p ≤ (4399/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-962053907/5000000000 : ℝ)*x 0 + (5601241249/10000000000 : ℝ)*x 1 + (5078739231/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (962053907/5000000000 : ℝ)^4399 ≤ (2333937908149/20000000000000 : ℝ)^3375 := by
    have hnat : (962053907 : ℕ)^4399*20000000000000^3375 ≤ 2333937908149^3375*5000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      962053907 5000000000 2333937908149 20000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5601241249/10000000000 : ℝ)^4399 ≤ (23489937879047/50000000000000 : ℝ)^3375 := by
    have hnat : (5601241249 : ℕ)^4399*50000000000000^3375 ≤ 23489937879047^3375*10000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5601241249 10000000000 23489937879047 50000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5078739231/10000000000 : ℝ)^4399 ≤ (41350434685027/100000000000000 : ℝ)^3375 := by
    have hnat : (5078739231 : ℕ)^4399*100000000000000^3375 ≤ 41350434685027^3375*10000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5078739231 10000000000 41350434685027 100000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4399/1024 : ℝ)) 4399 3375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-962053907/5000000000 : ℝ), (5601241249/10000000000 : ℝ), (5078739231/10000000000 : ℝ)] ![(2333937908149/20000000000000 : ℝ), (23489937879047/50000000000000 : ℝ), (41350434685027/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-962053907/5000000000 : ℝ)|^4399 ≤ (2333937908149/20000000000000 : ℝ)^3375
        have hw : |(-962053907/5000000000 : ℝ)|=(962053907/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5601241249/10000000000 : ℝ)|^4399 ≤ (23489937879047/50000000000000 : ℝ)^3375
        have hw : |(5601241249/10000000000 : ℝ)|=(5601241249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5078739231/10000000000 : ℝ)|^4399 ≤ (41350434685027/100000000000000 : ℝ)^3375
        have hw : |(5078739231/10000000000 : ℝ)|=(5078739231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1439_s1_1 (p : ℝ) (hpa : (2199/512 : ℝ) ≤ p) (hpb : p ≤ (4399/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5395808009/10000000000 : ℝ)*x 0 + (-1100382519/5000000000 : ℝ)*x 1 + (2539370351/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5395808009/10000000000 : ℝ)^4399 ≤ (8949328253319/20000000000000 : ℝ)^3375 := by
    have hnat : (5395808009 : ℕ)^4399*20000000000000^3375 ≤ 8949328253319^3375*10000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5395808009 10000000000 8949328253319 20000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1100382519/5000000000 : ℝ)^4399 ≤ (69514542131/500000000000 : ℝ)^3375 := by
    have hnat : (1100382519 : ℕ)^4399*500000000000^3375 ≤ 69514542131^3375*5000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1100382519 5000000000 69514542131 500000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2539370351/5000000000 : ℝ)^4399 ≤ (8270090059107/20000000000000 : ℝ)^3375 := by
    have hnat : (2539370351 : ℕ)^4399*20000000000000^3375 ≤ 8270090059107^3375*5000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2539370351 5000000000 8270090059107 20000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4399/1024 : ℝ)) 4399 3375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5395808009/10000000000 : ℝ), (-1100382519/5000000000 : ℝ), (2539370351/5000000000 : ℝ)] ![(8949328253319/20000000000000 : ℝ), (69514542131/500000000000 : ℝ), (8270090059107/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5395808009/10000000000 : ℝ)|^4399 ≤ (8949328253319/20000000000000 : ℝ)^3375
        have hw : |(5395808009/10000000000 : ℝ)|=(5395808009/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1100382519/5000000000 : ℝ)|^4399 ≤ (69514542131/500000000000 : ℝ)^3375
        have hw : |(-1100382519/5000000000 : ℝ)|=(1100382519/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2539370351/5000000000 : ℝ)|^4399 ≤ (8270090059107/20000000000000 : ℝ)^3375
        have hw : |(2539370351/5000000000 : ℝ)|=(2539370351/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1439_s1_2 (p : ℝ) (hpa : (2199/512 : ℝ) ≤ p) (hpb : p ≤ (4399/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5395809197/10000000000 : ℝ)*x 0 + (5078739357/10000000000 : ℝ)*x 1 + (-550191303/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5395809197/10000000000 : ℝ)^4399 ≤ (44746654107647/100000000000000 : ℝ)^3375 := by
    have hnat : (5395809197 : ℕ)^4399*100000000000000^3375 ≤ 44746654107647^3375*10000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5395809197 10000000000 44746654107647 100000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5078739357/10000000000 : ℝ)^4399 ≤ (41350436022161/100000000000000 : ℝ)^3375 := by
    have hnat : (5078739357 : ℕ)^4399*100000000000000^3375 ≤ 41350436022161^3375*10000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5078739357 10000000000 41350436022161 100000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (550191303/2500000000 : ℝ)^4399 ≤ (347572746473/2500000000000 : ℝ)^3375 := by
    have hnat : (550191303 : ℕ)^4399*2500000000000^3375 ≤ 347572746473^3375*2500000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      550191303 2500000000 347572746473 2500000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4399/1024 : ℝ)) 4399 3375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5395809197/10000000000 : ℝ), (5078739357/10000000000 : ℝ), (-550191303/2500000000 : ℝ)] ![(44746654107647/100000000000000 : ℝ), (41350436022161/100000000000000 : ℝ), (347572746473/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5395809197/10000000000 : ℝ)|^4399 ≤ (44746654107647/100000000000000 : ℝ)^3375
        have hw : |(5395809197/10000000000 : ℝ)|=(5395809197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5078739357/10000000000 : ℝ)|^4399 ≤ (41350436022161/100000000000000 : ℝ)^3375
        have hw : |(5078739357/10000000000 : ℝ)|=(5078739357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-550191303/2500000000 : ℝ)|^4399 ≤ (347572746473/2500000000000 : ℝ)^3375
        have hw : |(-550191303/2500000000 : ℝ)|=(550191303/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1439_s1_3 (p : ℝ) (hpa : (2199/512 : ℝ) ≤ p) (hpb : p ≤ (4399/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4274820043/10000000000 : ℝ)*x 0 + (748206347/2000000000 : ℝ)*x 1 + (4875517809/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4274820043/10000000000 : ℝ)^4399 ≤ (8258013403329/25000000000000 : ℝ)^3375 := by
    have hnat : (4274820043 : ℕ)^4399*25000000000000^3375 ≤ 8258013403329^3375*10000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4274820043 10000000000 8258013403329 25000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (748206347/2000000000 : ℝ)^4399 ≤ (13880458821477/50000000000000 : ℝ)^3375 := by
    have hnat : (748206347 : ℕ)^4399*50000000000000^3375 ≤ 13880458821477^3375*2000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      748206347 2000000000 13880458821477 50000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4875517809/10000000000 : ℝ)^4399 ≤ (392070287249/1000000000000 : ℝ)^3375 := by
    have hnat : (4875517809 : ℕ)^4399*1000000000000^3375 ≤ 392070287249^3375*10000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4875517809 10000000000 392070287249 1000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4399/1024 : ℝ)) 4399 3375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4274820043/10000000000 : ℝ), (748206347/2000000000 : ℝ), (4875517809/10000000000 : ℝ)] ![(8258013403329/25000000000000 : ℝ), (13880458821477/50000000000000 : ℝ), (392070287249/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4274820043/10000000000 : ℝ)|^4399 ≤ (8258013403329/25000000000000 : ℝ)^3375
        have hw : |(4274820043/10000000000 : ℝ)|=(4274820043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(748206347/2000000000 : ℝ)|^4399 ≤ (13880458821477/50000000000000 : ℝ)^3375
        have hw : |(748206347/2000000000 : ℝ)|=(748206347/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4875517809/10000000000 : ℝ)|^4399 ≤ (392070287249/1000000000000 : ℝ)^3375
        have hw : |(4875517809/10000000000 : ℝ)|=(4875517809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1439_s1_4 (p : ℝ) (hpa : (2199/512 : ℝ) ≤ p) (hpb : p ≤ (4399/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-60140389/312500000 : ℝ)*x 0 + (1016963663/2000000000 : ℝ)*x 1 + (5595059879/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (60140389/312500000 : ℝ)^4399 ≤ (2918182555549/25000000000000 : ℝ)^3375 := by
    have hnat : (60140389 : ℕ)^4399*25000000000000^3375 ≤ 2918182555549^3375*312500000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      60140389 312500000 2918182555549 25000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1016963663/2000000000 : ℝ)^4399 ≤ (41414958691507/100000000000000 : ℝ)^3375 := by
    have hnat : (1016963663 : ℕ)^4399*100000000000000^3375 ≤ 41414958691507^3375*2000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1016963663 2000000000 41414958691507 100000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5595059879/10000000000 : ℝ)^4399 ≤ (46912311069747/100000000000000 : ℝ)^3375 := by
    have hnat : (5595059879 : ℕ)^4399*100000000000000^3375 ≤ 46912311069747^3375*10000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5595059879 10000000000 46912311069747 100000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4399/1024 : ℝ)) 4399 3375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-60140389/312500000 : ℝ), (1016963663/2000000000 : ℝ), (5595059879/10000000000 : ℝ)] ![(2918182555549/25000000000000 : ℝ), (41414958691507/100000000000000 : ℝ), (46912311069747/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-60140389/312500000 : ℝ)|^4399 ≤ (2918182555549/25000000000000 : ℝ)^3375
        have hw : |(-60140389/312500000 : ℝ)|=(60140389/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1016963663/2000000000 : ℝ)|^4399 ≤ (41414958691507/100000000000000 : ℝ)^3375
        have hw : |(1016963663/2000000000 : ℝ)|=(1016963663/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5595059879/10000000000 : ℝ)|^4399 ≤ (46912311069747/100000000000000 : ℝ)^3375
        have hw : |(5595059879/10000000000 : ℝ)|=(5595059879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1439_s1_5 (p : ℝ) (hpa : (2199/512 : ℝ) ≤ p) (hpb : p ≤ (4399/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2629596181/5000000000 : ℝ)*x 0 + (-421111343/2500000000 : ℝ)*x 1 + (2797529951/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2629596181/5000000000 : ℝ)^4399 ≤ (43275672981831/100000000000000 : ℝ)^3375 := by
    have hnat : (2629596181 : ℕ)^4399*100000000000000^3375 ≤ 43275672981831^3375*5000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2629596181 5000000000 43275672981831 100000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (421111343/2500000000 : ℝ)^4399 ≤ (15331274513/156250000000 : ℝ)^3375 := by
    have hnat : (421111343 : ℕ)^4399*156250000000^3375 ≤ 15331274513^3375*2500000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      421111343 2500000000 15331274513 156250000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2797529951/5000000000 : ℝ)^4399 ≤ (46912311321103/100000000000000 : ℝ)^3375 := by
    have hnat : (2797529951 : ℕ)^4399*100000000000000^3375 ≤ 46912311321103^3375*5000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2797529951 5000000000 46912311321103 100000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4399/1024 : ℝ)) 4399 3375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2629596181/5000000000 : ℝ), (-421111343/2500000000 : ℝ), (2797529951/5000000000 : ℝ)] ![(43275672981831/100000000000000 : ℝ), (15331274513/156250000000 : ℝ), (46912311321103/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2629596181/5000000000 : ℝ)|^4399 ≤ (43275672981831/100000000000000 : ℝ)^3375
        have hw : |(2629596181/5000000000 : ℝ)|=(2629596181/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-421111343/2500000000 : ℝ)|^4399 ≤ (15331274513/156250000000 : ℝ)^3375
        have hw : |(-421111343/2500000000 : ℝ)|=(421111343/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2797529951/5000000000 : ℝ)|^4399 ≤ (46912311321103/100000000000000 : ℝ)^3375
        have hw : |(2797529951/5000000000 : ℝ)|=(2797529951/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1439_s1_6 (p : ℝ) (hpa : (2199/512 : ℝ) ≤ p) (hpb : p ≤ (4399/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5259192291/10000000000 : ℝ)*x 0 + (2797529931/5000000000 : ℝ)*x 1 + (-1684445529/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5259192291/10000000000 : ℝ)^4399 ≤ (21637836110171/50000000000000 : ℝ)^3375 := by
    have hnat : (5259192291 : ℕ)^4399*50000000000000^3375 ≤ 21637836110171^3375*10000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5259192291 10000000000 21637836110171 50000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2797529931/5000000000 : ℝ)^4399 ≤ (23456155441981/50000000000000 : ℝ)^3375 := by
    have hnat : (2797529931 : ℕ)^4399*50000000000000^3375 ≤ 23456155441981^3375*5000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2797529931 5000000000 23456155441981 50000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1684445529/10000000000 : ℝ)^4399 ≤ (9812016880333/100000000000000 : ℝ)^3375 := by
    have hnat : (1684445529 : ℕ)^4399*100000000000000^3375 ≤ 9812016880333^3375*10000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1684445529 10000000000 9812016880333 100000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4399/1024 : ℝ)) 4399 3375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5259192291/10000000000 : ℝ), (2797529931/5000000000 : ℝ), (-1684445529/10000000000 : ℝ)] ![(21637836110171/50000000000000 : ℝ), (23456155441981/50000000000000 : ℝ), (9812016880333/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5259192291/10000000000 : ℝ)|^4399 ≤ (21637836110171/50000000000000 : ℝ)^3375
        have hw : |(5259192291/10000000000 : ℝ)|=(5259192291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2797529931/5000000000 : ℝ)|^4399 ≤ (23456155441981/50000000000000 : ℝ)^3375
        have hw : |(2797529931/5000000000 : ℝ)|=(2797529931/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1684445529/10000000000 : ℝ)|^4399 ≤ (9812016880333/100000000000000 : ℝ)^3375
        have hw : |(-1684445529/10000000000 : ℝ)|=(1684445529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1439_s1_7 (p : ℝ) (hpa : (2199/512 : ℝ) ≤ p) (hpb : p ≤ (4399/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4275655643/10000000000 : ℝ)*x 0 + (4862319843/10000000000 : ℝ)*x 1 + (3754450789/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4275655643/10000000000 : ℝ)^4399 ≤ (2065029355077/6250000000000 : ℝ)^3375 := by
    have hnat : (4275655643 : ℕ)^4399*6250000000000^3375 ≤ 2065029355077^3375*10000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4275655643 10000000000 2065029355077 6250000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4862319843/10000000000 : ℝ)^4399 ≤ (39068751110793/100000000000000 : ℝ)^3375 := by
    have hnat : (4862319843 : ℕ)^4399*100000000000000^3375 ≤ 39068751110793^3375*10000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4862319843 10000000000 39068751110793 100000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3754450789/10000000000 : ℝ)^4399 ≤ (3486347398879/12500000000000 : ℝ)^3375 := by
    have hnat : (3754450789 : ℕ)^4399*12500000000000^3375 ≤ 3486347398879^3375*10000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3754450789 10000000000 3486347398879 12500000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4399/1024 : ℝ)) 4399 3375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4275655643/10000000000 : ℝ), (4862319843/10000000000 : ℝ), (3754450789/10000000000 : ℝ)] ![(2065029355077/6250000000000 : ℝ), (39068751110793/100000000000000 : ℝ), (3486347398879/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4275655643/10000000000 : ℝ)|^4399 ≤ (2065029355077/6250000000000 : ℝ)^3375
        have hw : |(4275655643/10000000000 : ℝ)|=(4275655643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4862319843/10000000000 : ℝ)|^4399 ≤ (39068751110793/100000000000000 : ℝ)^3375
        have hw : |(4862319843/10000000000 : ℝ)|=(4862319843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3754450789/10000000000 : ℝ)|^4399 ≤ (3486347398879/12500000000000 : ℝ)^3375
        have hw : |(3754450789/10000000000 : ℝ)|=(3754450789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1439_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2199/512 : ℝ) ≤ p) (hpb : p ≤ (4399/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158563157/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (26189/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1059/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (7733/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (939/5000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (26189/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1059/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (26189/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1059/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (26189/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1059/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (26189/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1059/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (26189/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1059/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (26189/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1059/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1059/50000 : ℝ) ^ (2199/512 : ℝ) ≤ (6456286098021/100000000000000000000 : ℝ) := by
    have hpowers : (1059/50000 : ℝ)^2199 ≤ (6456286098021/100000000000000000000 : ℝ)^512 := by
      have hnat : (1059 : ℕ)^2199*100000000000000000000^512 ≤ 6456286098021^512*50000^2199 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1059 50000 6456286098021 100000000000000000000 2199 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1059/50000 : ℝ)) (X := (6456286098021/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2199 512 (by norm_num) hpowers
    exact h
  have hpowhi : (26189/100000 : ℝ) ^ (2199/512 : ℝ) ≤ (63371822609269607/20000000000000000000 : ℝ) := by
    have hpowers : (26189/100000 : ℝ)^2199 ≤ (63371822609269607/20000000000000000000 : ℝ)^512 := by
      have hnat : (26189 : ℕ)^2199*20000000000000000000^512 ≤ 63371822609269607^512*100000^2199 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26189 100000 63371822609269607 20000000000000000000 2199 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (26189/100000 : ℝ)) (X := (63371822609269607/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2199 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000006456286098021/50000000000000000000 : ℝ) ≤ (2000000060129483/2000000000000000 : ℝ) ^ (2199/512 : ℝ) := by
    have hpowers : (50000006456286098021/50000000000000000000 : ℝ)^512 ≤ (2000000060129483/2000000000000000 : ℝ)^2199 := by
      have hnat : (50000006456286098021 : ℕ)^512*2000000000000000^2199 ≤ 2000000060129483^2199*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000006456286098021 50000000000000000000 2000000060129483 2000000000000000 512 2199 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000000060129483/2000000000000000 : ℝ)) (X := (50000006456286098021/50000000000000000000 : ℝ)) (by norm_num) 2199 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (12539608196166555757/12500000000000000000 : ℝ) ≤ (400294749160531/400000000000000 : ℝ) ^ (2199/512 : ℝ) := by
    have hpowers : (12539608196166555757/12500000000000000000 : ℝ)^512 ≤ (400294749160531/400000000000000 : ℝ)^2199 := by
      have hnat : (12539608196166555757 : ℕ)^512*400000000000000^2199 ≤ 400294749160531^2199*12500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12539608196166555757 12500000000000000000 400294749160531 400000000000000 512 2199 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400294749160531/400000000000000 : ℝ)) (X := (12539608196166555757/12500000000000000000 : ℝ)) (by norm_num) 2199 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (10063371822609269607/10000000000000000000 : ℝ) ≤ (2002947431475827/2000000000000000 : ℝ) ^ (2199/512 : ℝ) := by
    have hpowers : (10063371822609269607/10000000000000000000 : ℝ)^512 ≤ (2002947431475827/2000000000000000 : ℝ)^2199 := by
      have hnat : (10063371822609269607 : ℕ)^512*2000000000000000^2199 ≤ 2002947431475827^2199*10000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10063371822609269607 10000000000000000000 2002947431475827 2000000000000000 512 2199 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2002947431475827/2000000000000000 : ℝ)) (X := (10063371822609269607/10000000000000000000 : ℝ)) (by norm_num) 2199 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6456286098021/100000000000000000000 : ℝ) ≤ ((48135758914865228701/48142000000000000000 : ℝ)+2*(368421418293/120355000000000 : ℝ)*(1059/50000 : ℝ))^(2199/512 : ℝ) := by
    rw [show (48135758914865228701/48142000000000000000 : ℝ)+2*(368421418293/120355000000000 : ℝ)*(1059/50000 : ℝ)=(2000000060129483/2000000000000000 : ℝ) by norm_num, show 1+2*(6456286098021/100000000000000000000 : ℝ)=(50000006456286098021/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(63371822609269607/20000000000000000000 : ℝ)+(6456286098021/100000000000000000000 : ℝ) ≤ ((48135758914865228701/48142000000000000000 : ℝ)+(368421418293/120355000000000 : ℝ)*((26189/100000 : ℝ)+(1059/50000 : ℝ)))^(2199/512 : ℝ) := by
    rw [show (48135758914865228701/48142000000000000000 : ℝ)+(368421418293/120355000000000 : ℝ)*((26189/100000 : ℝ)+(1059/50000 : ℝ))=(400294749160531/400000000000000 : ℝ) by norm_num, show 1+(63371822609269607/20000000000000000000 : ℝ)+(6456286098021/100000000000000000000 : ℝ)=(12539608196166555757/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(63371822609269607/20000000000000000000 : ℝ) ≤ ((48135758914865228701/48142000000000000000 : ℝ)+2*(368421418293/120355000000000 : ℝ)*(26189/100000 : ℝ))^(2199/512 : ℝ) := by
    rw [show (48135758914865228701/48142000000000000000 : ℝ)+2*(368421418293/120355000000000 : ℝ)*(26189/100000 : ℝ)=(2002947431475827/2000000000000000 : ℝ) by norm_num, show 1+2*(63371822609269607/20000000000000000000 : ℝ)=(10063371822609269607/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (48135758914865228701/48142000000000000000 : ℝ)*(X 1 0+X 2 0)+(368421418293/120355000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2199/512 : ℝ)) (lo := (1059/50000 : ℝ)) (hi := (26189/100000 : ℝ)) (c := (48135758914865228701/48142000000000000000 : ℝ)) (alpha := (368421418293/120355000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (48135758914865228701/48142000000000000000 : ℝ)*(X 0 1+X 2 1)+(368421418293/120355000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2199/512 : ℝ)) (lo := (1059/50000 : ℝ)) (hi := (26189/100000 : ℝ)) (c := (48135758914865228701/48142000000000000000 : ℝ)) (alpha := (368421418293/120355000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (48135758914865228701/48142000000000000000 : ℝ)*(X 0 2+X 1 2)+(368421418293/120355000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2199/512 : ℝ)) (lo := (1059/50000 : ℝ)) (hi := (26189/100000 : ℝ)) (c := (48135758914865228701/48142000000000000000 : ℝ)) (alpha := (368421418293/120355000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-962053907/5000000000 : ℝ)*X 0 0+(5601241249/10000000000 : ℝ)*X 0 1+(5078739231/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1439_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5395808009/10000000000 : ℝ)*X 1 0+(-1100382519/5000000000 : ℝ)*X 1 1+(2539370351/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1439_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5395809197/10000000000 : ℝ)*X 2 0+(5078739357/10000000000 : ℝ)*X 2 1+(-550191303/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1439_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4274820043/10000000000 : ℝ)*X 0 0+(748206347/2000000000 : ℝ)*X 0 1+(4875517809/10000000000 : ℝ)*X 0 2+(4274820043/10000000000 : ℝ)*X 1 0+(748206347/2000000000 : ℝ)*X 1 1+(4875517809/10000000000 : ℝ)*X 1 2+(4274820043/10000000000 : ℝ)*X 2 0+(748206347/2000000000 : ℝ)*X 2 1+(4875517809/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1439_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-60140389/312500000 : ℝ)*X 0 0+(1016963663/2000000000 : ℝ)*X 0 1+(5595059879/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1439_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2629596181/5000000000 : ℝ)*X 1 0+(-421111343/2500000000 : ℝ)*X 1 1+(2797529951/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1439_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5259192291/10000000000 : ℝ)*X 2 0+(2797529931/5000000000 : ℝ)*X 2 1+(-1684445529/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1439_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4275655643/10000000000 : ℝ)*X 0 0+(4862319843/10000000000 : ℝ)*X 0 1+(3754450789/10000000000 : ℝ)*X 0 2+(4275655643/10000000000 : ℝ)*X 1 0+(4862319843/10000000000 : ℝ)*X 1 1+(3754450789/10000000000 : ℝ)*X 1 2+(4275655643/10000000000 : ℝ)*X 2 0+(4862319843/10000000000 : ℝ)*X 2 1+(3754450789/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1439_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (23394589733058523192288379151/2407100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (8551623/50000000000000 : ℝ)*(base1) + (337879453/20000000000000 : ℝ)*(base19) + (1055391289/50000000000000 : ℝ)*(base23) + (40914959/25000000000000 : ℝ)*(upper3) + (88190827/50000000000000 : ℝ)*(upper5) + (1397686658988183/100000000000000 : ℝ)*(major0) + (1397686658988183/100000000000000 : ℝ)*(major1) + (1397686658988183/100000000000000 : ℝ)*(major2) + (95694239734057/5000000000000 : ℝ)*(sp0) + (956950652627867/50000000000000 : ℝ)*(sp1) + (1913900883870421/100000000000000 : ℝ)*(sp2) + (27545715545269/3125000000000 : ℝ)*(sp3) + (9108537553/50000000000000 : ℝ)*(sp4) + (7084805047/100000000000000 : ℝ)*(sp7) + (440734999678451/50000000000000 : ℝ)*(f.failure) + (1913902994653/100000000000 : ℝ)*(f.sum) + (30828921361369/24071000000000000000000000000 : ℝ)*base65 + (6561349919665159717/4814200000000000000000000000000000 : ℝ)*base68 + (24983053359060759717/4814200000000000000000000000000000 : ℝ)*base70 + (37497624903010840283/4814200000000000000000000000000000 : ℝ)*base71 + (48483620106763/24071000000000000000000000000 : ℝ)*base74 + (29799607163232440283/4814200000000000000000000000000000 : ℝ)*base75 + (21718177739910640283/4814200000000000000000000000000000 : ℝ)*base77 + (33246552338267440283/4814200000000000000000000000000000 : ℝ)*base79 + (79679710582437/24071000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (25429807/5000000000000000000000 : ℝ)*base89 + (25429807/5000000000000000000000 : ℝ)*base91 + (25429807/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5140492006416488472408834597/1203550000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (25660897/100000000000000 : ℝ)*(base1) + (243079971/25000000000000 : ℝ)*(base19) + (935694037/100000000000000 : ℝ)*(base23) + (13884041/12500000000000 : ℝ)*(upper3) + (83313637/100000000000000 : ℝ)*(upper5) + (715622385276899/50000000000000 : ℝ)*(major0) + (715622385276899/50000000000000 : ℝ)*(major1) + (715622385276899/50000000000000 : ℝ)*(major2) + (2976637319/50000000000000 : ℝ)*(sp1) + (2780906771/50000000000000 : ℝ)*(sp2) + (244981943501159/12500000000000 : ℝ)*(sp4) + (1959848596753853/100000000000000 : ℝ)*(sp5) + (489962256210199/25000000000000 : ℝ)*(sp6) + (451316925364027/50000000000000 : ℝ)*(sp7) + (902633876388951/100000000000000 : ℝ)*(f.failure) + (15678844178787/800000000000 : ℝ)*(f.sum) + (5876640216823/2407100000000000000000000000 : ℝ)*base66 + (446512445224321801/2407100000000000000000000000000000 : ℝ)*base68 + (18488787253517521801/2407100000000000000000000000000000 : ℝ)*base70 + (4574599998065121801/2407100000000000000000000000000000 : ℝ)*base72 + (50853571399523/12035500000000000000000000000 : ℝ)*base74 + (9452780937505078199/2407100000000000000000000000000000 : ℝ)*base75 + (18149379904672678199/2407100000000000000000000000000000 : ℝ)*base77 + (6789909293982921801/2407100000000000000000000000000000 : ℝ)*base80 + (84699583720311/12035500000000000000000000000 : ℝ)*base82 + (30478307/10000000000000000000000 : ℝ)*base89 + (30478307/10000000000000000000000 : ℝ)*base91 + (30478307/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1439_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2199/512 : ℝ) ≤ p) (hpb : p ≤ (4399/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158563157/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (26189/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1059/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (7733/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (939/5000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1439_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1439_s2_0 (p : ℝ) (hpa : (2199/512 : ℝ) ≤ p) (hpb : p ≤ (4399/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1956500679/10000000000 : ℝ)*x 0 + (2727979089/5000000000 : ℝ)*x 1 + (5203160043/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1956500679/10000000000 : ℝ)^4399 ≤ (1490801429667/12500000000000 : ℝ)^3375 := by
    have hnat : (1956500679 : ℕ)^4399*12500000000000^3375 ≤ 1490801429667^3375*10000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1956500679 10000000000 1490801429667 12500000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2727979089/5000000000 : ℝ)^4399 ≤ (2837368690829/6250000000000 : ℝ)^3375 := by
    have hnat : (2727979089 : ℕ)^4399*6250000000000^3375 ≤ 2837368690829^3375*5000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2727979089 5000000000 2837368690829 6250000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5203160043/10000000000 : ℝ)^4399 ≤ (42675689490469/100000000000000 : ℝ)^3375 := by
    have hnat : (5203160043 : ℕ)^4399*100000000000000^3375 ≤ 42675689490469^3375*10000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5203160043 10000000000 42675689490469 100000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4399/1024 : ℝ)) 4399 3375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1956500679/10000000000 : ℝ), (2727979089/5000000000 : ℝ), (5203160043/10000000000 : ℝ)] ![(1490801429667/12500000000000 : ℝ), (2837368690829/6250000000000 : ℝ), (42675689490469/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1956500679/10000000000 : ℝ)|^4399 ≤ (1490801429667/12500000000000 : ℝ)^3375
        have hw : |(-1956500679/10000000000 : ℝ)|=(1956500679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2727979089/5000000000 : ℝ)|^4399 ≤ (2837368690829/6250000000000 : ℝ)^3375
        have hw : |(2727979089/5000000000 : ℝ)|=(2727979089/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5203160043/10000000000 : ℝ)|^4399 ≤ (42675689490469/100000000000000 : ℝ)^3375
        have hw : |(5203160043/10000000000 : ℝ)|=(5203160043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1439_s2_1 (p : ℝ) (hpa : (2199/512 : ℝ) ≤ p) (hpb : p ≤ (4399/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5359510257/10000000000 : ℝ)*x 0 + (-2086507627/10000000000 : ℝ)*x 1 + (2601579937/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5359510257/10000000000 : ℝ)^4399 ≤ (44354701127569/100000000000000 : ℝ)^3375 := by
    have hnat : (5359510257 : ℕ)^4399*100000000000000^3375 ≤ 44354701127569^3375*10000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5359510257 10000000000 44354701127569 100000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2086507627/10000000000 : ℝ)^4399 ≤ (12969611170837/100000000000000 : ℝ)^3375 := by
    have hnat : (2086507627 : ℕ)^4399*100000000000000^3375 ≤ 12969611170837^3375*10000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2086507627 10000000000 12969611170837 100000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2601579937/5000000000 : ℝ)^4399 ≤ (42675687683793/100000000000000 : ℝ)^3375 := by
    have hnat : (2601579937 : ℕ)^4399*100000000000000^3375 ≤ 42675687683793^3375*5000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2601579937 5000000000 42675687683793 100000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4399/1024 : ℝ)) 4399 3375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5359510257/10000000000 : ℝ), (-2086507627/10000000000 : ℝ), (2601579937/5000000000 : ℝ)] ![(44354701127569/100000000000000 : ℝ), (12969611170837/100000000000000 : ℝ), (42675687683793/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5359510257/10000000000 : ℝ)|^4399 ≤ (44354701127569/100000000000000 : ℝ)^3375
        have hw : |(5359510257/10000000000 : ℝ)|=(5359510257/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2086507627/10000000000 : ℝ)|^4399 ≤ (12969611170837/100000000000000 : ℝ)^3375
        have hw : |(-2086507627/10000000000 : ℝ)|=(2086507627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2601579937/5000000000 : ℝ)|^4399 ≤ (42675687683793/100000000000000 : ℝ)^3375
        have hw : |(2601579937/5000000000 : ℝ)|=(2601579937/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1439_s2_2 (p : ℝ) (hpa : (2199/512 : ℝ) ≤ p) (hpb : p ≤ (4399/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (167484681/312500000 : ℝ)*x 0 + (325197523/625000000 : ℝ)*x 1 + (-1043253797/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (167484681/312500000 : ℝ)^4399 ≤ (44354696111683/100000000000000 : ℝ)^3375 := by
    have hnat : (167484681 : ℕ)^4399*100000000000000^3375 ≤ 44354696111683^3375*312500000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      167484681 312500000 44354696111683 100000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (325197523/625000000 : ℝ)^4399 ≤ (21337846482423/50000000000000 : ℝ)^3375 := by
    have hnat : (325197523 : ℕ)^4399*50000000000000^3375 ≤ 21337846482423^3375*625000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      325197523 625000000 21337846482423 50000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1043253797/5000000000 : ℝ)^4399 ≤ (6484805451737/50000000000000 : ℝ)^3375 := by
    have hnat : (1043253797 : ℕ)^4399*50000000000000^3375 ≤ 6484805451737^3375*5000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043253797 5000000000 6484805451737 50000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4399/1024 : ℝ)) 4399 3375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(167484681/312500000 : ℝ), (325197523/625000000 : ℝ), (-1043253797/5000000000 : ℝ)] ![(44354696111683/100000000000000 : ℝ), (21337846482423/50000000000000 : ℝ), (6484805451737/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(167484681/312500000 : ℝ)|^4399 ≤ (44354696111683/100000000000000 : ℝ)^3375
        have hw : |(167484681/312500000 : ℝ)|=(167484681/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(325197523/625000000 : ℝ)|^4399 ≤ (21337846482423/50000000000000 : ℝ)^3375
        have hw : |(325197523/625000000 : ℝ)|=(325197523/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1043253797/5000000000 : ℝ)|^4399 ≤ (6484805451737/50000000000000 : ℝ)^3375
        have hw : |(-1043253797/5000000000 : ℝ)|=(1043253797/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1439_s2_3 (p : ℝ) (hpa : (2199/512 : ℝ) ≤ p) (hpb : p ≤ (4399/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (429770989/1000000000 : ℝ)*x 0 + (503887053/1250000000 : ℝ)*x 1 + (4579988397/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (429770989/1000000000 : ℝ)^4399 ≤ (8315694435317/25000000000000 : ℝ)^3375 := by
    have hnat : (429770989 : ℕ)^4399*25000000000000^3375 ≤ 8315694435317^3375*1000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      429770989 1000000000 8315694435317 25000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (503887053/1250000000 : ℝ)^4399 ≤ (7649722258209/25000000000000 : ℝ)^3375 := by
    have hnat : (503887053 : ℕ)^4399*25000000000000^3375 ≤ 7649722258209^3375*1250000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      503887053 1250000000 7649722258209 25000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4579988397/10000000000 : ℝ)^4399 ≤ (36138333202629/100000000000000 : ℝ)^3375 := by
    have hnat : (4579988397 : ℕ)^4399*100000000000000^3375 ≤ 36138333202629^3375*10000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4579988397 10000000000 36138333202629 100000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4399/1024 : ℝ)) 4399 3375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(429770989/1000000000 : ℝ), (503887053/1250000000 : ℝ), (4579988397/10000000000 : ℝ)] ![(8315694435317/25000000000000 : ℝ), (7649722258209/25000000000000 : ℝ), (36138333202629/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(429770989/1000000000 : ℝ)|^4399 ≤ (8315694435317/25000000000000 : ℝ)^3375
        have hw : |(429770989/1000000000 : ℝ)|=(429770989/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(503887053/1250000000 : ℝ)|^4399 ≤ (7649722258209/25000000000000 : ℝ)^3375
        have hw : |(503887053/1250000000 : ℝ)|=(503887053/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4579988397/10000000000 : ℝ)|^4399 ≤ (36138333202629/100000000000000 : ℝ)^3375
        have hw : |(4579988397/10000000000 : ℝ)|=(4579988397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1439_s2_4 (p : ℝ) (hpa : (2199/512 : ℝ) ≤ p) (hpb : p ≤ (4399/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-978272119/5000000000 : ℝ)*x 0 + (5204592187/10000000000 : ℝ)*x 1 + (5454514473/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (978272119/5000000000 : ℝ)^4399 ≤ (2981689381891/25000000000000 : ℝ)^3375 := by
    have hnat : (978272119 : ℕ)^4399*25000000000000^3375 ≤ 2981689381891^3375*5000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      978272119 5000000000 2981689381891 25000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5204592187/10000000000 : ℝ)^4399 ≤ (42691000307531/100000000000000 : ℝ)^3375 := by
    have hnat : (5204592187 : ℕ)^4399*100000000000000^3375 ≤ 42691000307531^3375*10000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5204592187 10000000000 42691000307531 100000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5454514473/10000000000 : ℝ)^4399 ≤ (9076448429537/20000000000000 : ℝ)^3375 := by
    have hnat : (5454514473 : ℕ)^4399*20000000000000^3375 ≤ 9076448429537^3375*10000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5454514473 10000000000 9076448429537 20000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4399/1024 : ℝ)) 4399 3375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-978272119/5000000000 : ℝ), (5204592187/10000000000 : ℝ), (5454514473/10000000000 : ℝ)] ![(2981689381891/25000000000000 : ℝ), (42691000307531/100000000000000 : ℝ), (9076448429537/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-978272119/5000000000 : ℝ)|^4399 ≤ (2981689381891/25000000000000 : ℝ)^3375
        have hw : |(-978272119/5000000000 : ℝ)|=(978272119/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5204592187/10000000000 : ℝ)|^4399 ≤ (42691000307531/100000000000000 : ℝ)^3375
        have hw : |(5204592187/10000000000 : ℝ)|=(5204592187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5454514473/10000000000 : ℝ)|^4399 ≤ (9076448429537/20000000000000 : ℝ)^3375
        have hw : |(5454514473/10000000000 : ℝ)|=(5454514473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1439_s2_5 (p : ℝ) (hpa : (2199/512 : ℝ) ≤ p) (hpb : p ≤ (4399/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5293712847/10000000000 : ℝ)*x 0 + (-367030469/2000000000 : ℝ)*x 1 + (68181441/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5293712847/10000000000 : ℝ)^4399 ≤ (8729255964031/20000000000000 : ℝ)^3375 := by
    have hnat : (5293712847 : ℕ)^4399*20000000000000^3375 ≤ 8729255964031^3375*10000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5293712847 10000000000 8729255964031 20000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (367030469/2000000000 : ℝ)^4399 ≤ (2194293853021/20000000000000 : ℝ)^3375 := by
    have hnat : (367030469 : ℕ)^4399*20000000000000^3375 ≤ 2194293853021^3375*2000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      367030469 2000000000 2194293853021 20000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (68181441/125000000 : ℝ)^4399 ≤ (22691125449603/50000000000000 : ℝ)^3375 := by
    have hnat : (68181441 : ℕ)^4399*50000000000000^3375 ≤ 22691125449603^3375*125000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      68181441 125000000 22691125449603 50000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4399/1024 : ℝ)) 4399 3375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5293712847/10000000000 : ℝ), (-367030469/2000000000 : ℝ), (68181441/125000000 : ℝ)] ![(8729255964031/20000000000000 : ℝ), (2194293853021/20000000000000 : ℝ), (22691125449603/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5293712847/10000000000 : ℝ)|^4399 ≤ (8729255964031/20000000000000 : ℝ)^3375
        have hw : |(5293712847/10000000000 : ℝ)|=(5293712847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-367030469/2000000000 : ℝ)|^4399 ≤ (2194293853021/20000000000000 : ℝ)^3375
        have hw : |(-367030469/2000000000 : ℝ)|=(367030469/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(68181441/125000000 : ℝ)|^4399 ≤ (22691125449603/50000000000000 : ℝ)^3375
        have hw : |(68181441/125000000 : ℝ)|=(68181441/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1439_s2_6 (p : ℝ) (hpa : (2199/512 : ℝ) ≤ p) (hpb : p ≤ (4399/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2646856223/5000000000 : ℝ)*x 0 + (1363628801/2500000000 : ℝ)*x 1 + (-458788251/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2646856223/5000000000 : ℝ)^4399 ≤ (5455784438851/12500000000000 : ℝ)^3375 := by
    have hnat : (2646856223 : ℕ)^4399*12500000000000^3375 ≤ 5455784438851^3375*5000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2646856223 5000000000 5455784438851 12500000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1363628801/2500000000 : ℝ)^4399 ≤ (45382250075023/100000000000000 : ℝ)^3375 := by
    have hnat : (1363628801 : ℕ)^4399*100000000000000^3375 ≤ 45382250075023^3375*2500000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1363628801 2500000000 45382250075023 100000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (458788251/2500000000 : ℝ)^4399 ≤ (2742868600079/25000000000000 : ℝ)^3375 := by
    have hnat : (458788251 : ℕ)^4399*25000000000000^3375 ≤ 2742868600079^3375*2500000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      458788251 2500000000 2742868600079 25000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4399/1024 : ℝ)) 4399 3375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2646856223/5000000000 : ℝ), (1363628801/2500000000 : ℝ), (-458788251/2500000000 : ℝ)] ![(5455784438851/12500000000000 : ℝ), (45382250075023/100000000000000 : ℝ), (2742868600079/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2646856223/5000000000 : ℝ)|^4399 ≤ (5455784438851/12500000000000 : ℝ)^3375
        have hw : |(2646856223/5000000000 : ℝ)|=(2646856223/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1363628801/2500000000 : ℝ)|^4399 ≤ (45382250075023/100000000000000 : ℝ)^3375
        have hw : |(1363628801/2500000000 : ℝ)|=(1363628801/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-458788251/2500000000 : ℝ)|^4399 ≤ (2742868600079/25000000000000 : ℝ)^3375
        have hw : |(-458788251/2500000000 : ℝ)|=(458788251/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1439_s2_7 (p : ℝ) (hpa : (2199/512 : ℝ) ≤ p) (hpb : p ≤ (4399/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (859560929/2000000000 : ℝ)*x 0 + (2288439867/5000000000 : ℝ)*x 1 + (4034230539/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (859560929/2000000000 : ℝ)^4399 ≤ (33263733625267/100000000000000 : ℝ)^3375 := by
    have hnat : (859560929 : ℕ)^4399*100000000000000^3375 ≤ 33263733625267^3375*2000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      859560929 2000000000 33263733625267 100000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2288439867/5000000000 : ℝ)^4399 ≤ (36106365395897/100000000000000 : ℝ)^3375 := by
    have hnat : (2288439867 : ℕ)^4399*100000000000000^3375 ≤ 36106365395897^3375*5000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2288439867 5000000000 36106365395897 100000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4034230539/10000000000 : ℝ)^4399 ≤ (3828737620367/12500000000000 : ℝ)^3375 := by
    have hnat : (4034230539 : ℕ)^4399*12500000000000^3375 ≤ 3828737620367^3375*10000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4034230539 10000000000 3828737620367 12500000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4399/1024 : ℝ)) 4399 3375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(859560929/2000000000 : ℝ), (2288439867/5000000000 : ℝ), (4034230539/10000000000 : ℝ)] ![(33263733625267/100000000000000 : ℝ), (36106365395897/100000000000000 : ℝ), (3828737620367/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(859560929/2000000000 : ℝ)|^4399 ≤ (33263733625267/100000000000000 : ℝ)^3375
        have hw : |(859560929/2000000000 : ℝ)|=(859560929/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2288439867/5000000000 : ℝ)|^4399 ≤ (36106365395897/100000000000000 : ℝ)^3375
        have hw : |(2288439867/5000000000 : ℝ)|=(2288439867/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4034230539/10000000000 : ℝ)|^4399 ≤ (3828737620367/12500000000000 : ℝ)^3375
        have hw : |(4034230539/10000000000 : ℝ)|=(4034230539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1439_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2199/512 : ℝ) ≤ p) (hpb : p ≤ (4399/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158563157/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (939/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (7733/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (521/5000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15769/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (939/5000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (7733/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (939/5000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (7733/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (939/5000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (7733/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (939/5000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (7733/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (939/5000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (7733/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (939/5000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (7733/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base29 : ((-1 : ℝ)*N 1+(-1 : ℝ)*N 2+(1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 0, f.sum]
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
  have hpowlo : (7733/100000 : ℝ) ^ (2199/512 : ℝ) ≤ (840449369778957/50000000000000000000 : ℝ) := by
    have hpowers : (7733/100000 : ℝ)^2199 ≤ (840449369778957/50000000000000000000 : ℝ)^512 := by
      have hnat : (7733 : ℕ)^2199*50000000000000000000^512 ≤ 840449369778957^512*100000^2199 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7733 100000 840449369778957 50000000000000000000 2199 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7733/100000 : ℝ)) (X := (840449369778957/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2199 512 (by norm_num) hpowers
    exact h
  have hpowhi : (939/5000 : ℝ) ^ (2199/512 : ℝ) ≤ (75959009457800563/100000000000000000000 : ℝ) := by
    have hpowers : (939/5000 : ℝ)^2199 ≤ (75959009457800563/100000000000000000000 : ℝ)^512 := by
      have hnat : (939 : ℕ)^2199*100000000000000000000^512 ≤ 75959009457800563^512*5000^2199 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        939 5000 75959009457800563 100000000000000000000 2199 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (939/5000 : ℝ)) (X := (75959009457800563/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2199 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000840449369778957/25000000000000000000 : ℝ) ≤ (10000078272765523/10000000000000000 : ℝ) ^ (2199/512 : ℝ) := by
    have hpowers : (25000840449369778957/25000000000000000000 : ℝ)^512 ≤ (10000078272765523/10000000000000000 : ℝ)^2199 := by
      have hnat : (25000840449369778957 : ℕ)^512*10000000000000000^2199 ≤ 10000078272765523^2199*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000840449369778957 25000000000000000000 10000078272765523 10000000000000000 512 2199 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000078272765523/10000000000000000 : ℝ)) (X := (25000840449369778957/25000000000000000000 : ℝ)) (by norm_num) 2199 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100077639908197358477/100000000000000000000 : ℝ) ≤ (10001807175980997/10000000000000000 : ℝ) ^ (2199/512 : ℝ) := by
    have hpowers : (100077639908197358477/100000000000000000000 : ℝ)^512 ≤ (10001807175980997/10000000000000000 : ℝ)^2199 := by
      have hnat : (100077639908197358477 : ℕ)^512*10000000000000000^2199 ≤ 10001807175980997^2199*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100077639908197358477 100000000000000000000 10001807175980997 10000000000000000 512 2199 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001807175980997/10000000000000000 : ℝ)) (X := (100077639908197358477/100000000000000000000 : ℝ)) (by norm_num) 2199 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50075959009457800563/50000000000000000000 : ℝ) ≤ (10003536079196471/10000000000000000 : ℝ) ^ (2199/512 : ℝ) := by
    have hpowers : (50075959009457800563/50000000000000000000 : ℝ)^512 ≤ (10003536079196471/10000000000000000 : ℝ)^2199 := by
      have hnat : (50075959009457800563 : ℕ)^512*10000000000000000^2199 ≤ 10003536079196471^2199*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50075959009457800563 50000000000000000000 10003536079196471 10000000000000000 512 2199 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003536079196471/10000000000000000 : ℝ)) (X := (50075959009457800563/50000000000000000000 : ℝ)) (by norm_num) 2199 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(840449369778957/50000000000000000000 : ℝ) ≤ ((110444125462110211697/110470000000000000000 : ℝ)+2*(864451607737/552350000000000 : ℝ)*(7733/100000 : ℝ))^(2199/512 : ℝ) := by
    rw [show (110444125462110211697/110470000000000000000 : ℝ)+2*(864451607737/552350000000000 : ℝ)*(7733/100000 : ℝ)=(10000078272765523/10000000000000000 : ℝ) by norm_num, show 1+2*(840449369778957/50000000000000000000 : ℝ)=(25000840449369778957/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(75959009457800563/100000000000000000000 : ℝ)+(840449369778957/50000000000000000000 : ℝ) ≤ ((110444125462110211697/110470000000000000000 : ℝ)+(864451607737/552350000000000 : ℝ)*((939/5000 : ℝ)+(7733/100000 : ℝ)))^(2199/512 : ℝ) := by
    rw [show (110444125462110211697/110470000000000000000 : ℝ)+(864451607737/552350000000000 : ℝ)*((939/5000 : ℝ)+(7733/100000 : ℝ))=(10001807175980997/10000000000000000 : ℝ) by norm_num, show 1+(75959009457800563/100000000000000000000 : ℝ)+(840449369778957/50000000000000000000 : ℝ)=(100077639908197358477/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(75959009457800563/100000000000000000000 : ℝ) ≤ ((110444125462110211697/110470000000000000000 : ℝ)+2*(864451607737/552350000000000 : ℝ)*(939/5000 : ℝ))^(2199/512 : ℝ) := by
    rw [show (110444125462110211697/110470000000000000000 : ℝ)+2*(864451607737/552350000000000 : ℝ)*(939/5000 : ℝ)=(10003536079196471/10000000000000000 : ℝ) by norm_num, show 1+2*(75959009457800563/100000000000000000000 : ℝ)=(50075959009457800563/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (110444125462110211697/110470000000000000000 : ℝ)*(X 1 0+X 2 0)+(864451607737/552350000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2199/512 : ℝ)) (lo := (7733/100000 : ℝ)) (hi := (939/5000 : ℝ)) (c := (110444125462110211697/110470000000000000000 : ℝ)) (alpha := (864451607737/552350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (110444125462110211697/110470000000000000000 : ℝ)*(X 0 1+X 2 1)+(864451607737/552350000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2199/512 : ℝ)) (lo := (7733/100000 : ℝ)) (hi := (939/5000 : ℝ)) (c := (110444125462110211697/110470000000000000000 : ℝ)) (alpha := (864451607737/552350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (110444125462110211697/110470000000000000000 : ℝ)*(X 0 2+X 1 2)+(864451607737/552350000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2199/512 : ℝ)) (lo := (7733/100000 : ℝ)) (hi := (939/5000 : ℝ)) (c := (110444125462110211697/110470000000000000000 : ℝ)) (alpha := (864451607737/552350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1956500679/10000000000 : ℝ)*X 0 0+(2727979089/5000000000 : ℝ)*X 0 1+(5203160043/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1439_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5359510257/10000000000 : ℝ)*X 1 0+(-2086507627/10000000000 : ℝ)*X 1 1+(2601579937/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1439_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((167484681/312500000 : ℝ)*X 2 0+(325197523/625000000 : ℝ)*X 2 1+(-1043253797/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1439_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((429770989/1000000000 : ℝ)*X 0 0+(503887053/1250000000 : ℝ)*X 0 1+(4579988397/10000000000 : ℝ)*X 0 2+(429770989/1000000000 : ℝ)*X 1 0+(503887053/1250000000 : ℝ)*X 1 1+(4579988397/10000000000 : ℝ)*X 1 2+(429770989/1000000000 : ℝ)*X 2 0+(503887053/1250000000 : ℝ)*X 2 1+(4579988397/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1439_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-978272119/5000000000 : ℝ)*X 0 0+(5204592187/10000000000 : ℝ)*X 0 1+(5454514473/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1439_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5293712847/10000000000 : ℝ)*X 1 0+(-367030469/2000000000 : ℝ)*X 1 1+(68181441/125000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1439_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2646856223/5000000000 : ℝ)*X 2 0+(1363628801/2500000000 : ℝ)*X 2 1+(-458788251/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1439_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((859560929/2000000000 : ℝ)*X 0 0+(2288439867/5000000000 : ℝ)*X 0 1+(4034230539/10000000000 : ℝ)*X 0 2+(859560929/2000000000 : ℝ)*X 1 0+(2288439867/5000000000 : ℝ)*X 1 1+(4034230539/10000000000 : ℝ)*X 1 2+(859560929/2000000000 : ℝ)*X 2 0+(2288439867/5000000000 : ℝ)*X 2 1+(4034230539/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1439_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (27525803923075637203434816087/2761750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (738976867/50000000000000 : ℝ)*(base19) + (862333747/100000000000000 : ℝ)*(base23) + (29199907/20000000000000 : ℝ)*(lower2) + (40861117/12500000000000 : ℝ)*(upper3) + (7572643/10000000000000 : ℝ)*(upper5) + (2888812735674957/100000000000000 : ℝ)*(major0) + (2888812735674957/100000000000000 : ℝ)*(major1) + (2888812735674957/100000000000000 : ℝ)*(major2) + (494467970893791/12500000000000 : ℝ)*(sp0) + (395575482963833/10000000000000 : ℝ)*(sp1) + (3955755445258317/100000000000000 : ℝ)*(sp2) + (455464794974371/25000000000000 : ℝ)*(sp3) + (12540441737/100000000000000 : ℝ)*(sp4) + (9651633763/100000000000000 : ℝ)*(sp7) + (1821868831531247/100000000000000 : ℝ)*(f.failure) + (30904346153063/781250000000 : ℝ)*(f.sum) + (410254906182023/55235000000000000000000000000 : ℝ)*base65 + (131905403949753827971/11047000000000000000000000000000000 : ℝ)*base68 + (77046417858256827971/11047000000000000000000000000000000 : ℝ)*base70 + (9150985651778172029/11047000000000000000000000000000000 : ℝ)*base71 + (115326728046081/27617500000000000000000000000 : ℝ)*base74 + (184032931058861827971/11047000000000000000000000000000000 : ℝ)*base76 + (20627188837159827971/11047000000000000000000000000000000 : ℝ)*base78 + (52487299737044827971/11047000000000000000000000000000000 : ℝ)*base80 + (239500856604473/55235000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (31533221/10000000000000000000000 : ℝ)*base90 + (31533221/10000000000000000000000 : ℝ)*base92 + (31533221/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2984422587099952023532445517/690437500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (11718137/10000000000000 : ℝ)*(base21) + (8016307/12500000000000 : ℝ)*(base29) + (1909923/2500000000000 : ℝ)*(upper3) + (35666659/25000000000000 : ℝ)*(lower4) + (36525344158869/1250000000000 : ℝ)*(major0) + (365253449604997/12500000000000 : ℝ)*(major1) + (365253449604997/12500000000000 : ℝ)*(major2) + (8419288379/100000000000000 : ℝ)*(sp1) + (685090407/25000000000000 : ℝ)*(sp2) + (681552699/25000000000000 : ℝ)*(sp3) + (2000619408270807/50000000000000 : ℝ)*(sp4) + (200061516656139/5000000000000 : ℝ)*(sp5) + (2000617947434079/50000000000000 : ℝ)*(sp6) + (921406753421941/50000000000000 : ℝ)*(sp7) + (921408116527339/50000000000000 : ℝ)*(f.failure) + (2000619408270807/50000000000000 : ℝ)*(f.sum) + (33945579843953/27617500000000000000000000000 : ℝ)*base66 + (941531952114400091/1380875000000000000000000000000000 : ℝ)*base68 + (5410285273706150091/1380875000000000000000000000000000 : ℝ)*base70 + (3165149444717516807/138087500000000000000000000000000 : ℝ)*base72 + (218255099443187/55235000000000000000000000000 : ℝ)*base73 + (3808426049098950091/1380875000000000000000000000000000 : ℝ)*base76 + (460705450801354307/138087500000000000000000000000000 : ℝ)*base78 + (14336982364015549909/1380875000000000000000000000000000 : ℝ)*base79 + (34273601107379/27617500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/50000000000000 : ℝ)*base88 + (51350777/5000000000000000000000 : ℝ)*base90 + (51350777/5000000000000000000000 : ℝ)*base92 + (51350777/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1439_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2199/512 : ℝ) ≤ p) (hpb : p ≤ (4399/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158563157/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (939/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (7733/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (521/5000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15769/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1439_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1439_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2199/512 : ℝ) ≤ p) (hpb : p ≤ (4399/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158563157/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (521/5000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15769/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1439_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1439_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1439_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2199/512 : ℝ) ≤ p) (hpb : p ≤ (4399/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158563157/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (521/5000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15769/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1439_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
