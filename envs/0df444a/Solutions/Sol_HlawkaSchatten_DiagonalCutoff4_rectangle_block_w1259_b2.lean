-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1259_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:53:37.151555+00:00
-- url     : https://prove2.me/submissions/3ca1fc80-5a37-44fd-a06c-f22c1927bd55

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
theorem support_rectangle_w1259_s6_0 (p : ℝ) (hpa : (8451/2048 : ℝ) ≤ p) (hpb : p ≤ (2113/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-132009087/625000000 : ℝ)*x 0 + (2695525953/5000000000 : ℝ)*x 1 + (329204727/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (132009087/625000000 : ℝ)^2113 ≤ (12846073429563/100000000000000 : ℝ)^1601 := by
    have hnat : (132009087 : ℕ)^2113*100000000000000^1601 ≤ 12846073429563^1601*625000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132009087 625000000 12846073429563 100000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2695525953/5000000000 : ℝ)^2113 ≤ (44244844118153/100000000000000 : ℝ)^1601 := by
    have hnat : (2695525953 : ℕ)^2113*100000000000000^1601 ≤ 44244844118153^1601*5000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695525953 5000000000 44244844118153 100000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (329204727/625000000 : ℝ)^2113 ≤ (42909082432919/100000000000000 : ℝ)^1601 := by
    have hnat : (329204727 : ℕ)^2113*100000000000000^1601 ≤ 42909082432919^1601*625000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      329204727 625000000 42909082432919 100000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2113/512 : ℝ)) 2113 1601 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-132009087/625000000 : ℝ), (2695525953/5000000000 : ℝ), (329204727/625000000 : ℝ)] ![(12846073429563/100000000000000 : ℝ), (44244844118153/100000000000000 : ℝ), (42909082432919/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-132009087/625000000 : ℝ)|^2113 ≤ (12846073429563/100000000000000 : ℝ)^1601
        have hw : |(-132009087/625000000 : ℝ)|=(132009087/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2695525953/5000000000 : ℝ)|^2113 ≤ (44244844118153/100000000000000 : ℝ)^1601
        have hw : |(2695525953/5000000000 : ℝ)|=(2695525953/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(329204727/625000000 : ℝ)|^2113 ≤ (42909082432919/100000000000000 : ℝ)^1601
        have hw : |(329204727/625000000 : ℝ)|=(329204727/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1259_s6_1 (p : ℝ) (hpa : (8451/2048 : ℝ) ≤ p) (hpb : p ≤ (2113/512 : ℝ)) (x : Fin 3 → ℝ) :
    (334016301/625000000 : ℝ)*x 0 + (-543725399/2500000000 : ℝ)*x 1 + (1316818907/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (334016301/625000000 : ℝ)^2113 ≤ (21869360518687/50000000000000 : ℝ)^1601 := by
    have hnat : (334016301 : ℕ)^2113*50000000000000^1601 ≤ 21869360518687^1601*625000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334016301 625000000 21869360518687 50000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (543725399/2500000000 : ℝ)^2113 ≤ (13352196561903/100000000000000 : ℝ)^1601 := by
    have hnat : (543725399 : ℕ)^2113*100000000000000^1601 ≤ 13352196561903^1601*2500000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      543725399 2500000000 13352196561903 100000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316818907/2500000000 : ℝ)^2113 ≤ (42909082389913/100000000000000 : ℝ)^1601 := by
    have hnat : (1316818907 : ℕ)^2113*100000000000000^1601 ≤ 42909082389913^1601*2500000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316818907 2500000000 42909082389913 100000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2113/512 : ℝ)) 2113 1601 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(334016301/625000000 : ℝ), (-543725399/2500000000 : ℝ), (1316818907/2500000000 : ℝ)] ![(21869360518687/50000000000000 : ℝ), (13352196561903/100000000000000 : ℝ), (42909082389913/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(334016301/625000000 : ℝ)|^2113 ≤ (21869360518687/50000000000000 : ℝ)^1601
        have hw : |(334016301/625000000 : ℝ)|=(334016301/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-543725399/2500000000 : ℝ)|^2113 ≤ (13352196561903/100000000000000 : ℝ)^1601
        have hw : |(-543725399/2500000000 : ℝ)|=(543725399/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316818907/2500000000 : ℝ)|^2113 ≤ (42909082389913/100000000000000 : ℝ)^1601
        have hw : |(1316818907/2500000000 : ℝ)|=(1316818907/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1259_s6_2 (p : ℝ) (hpa : (8451/2048 : ℝ) ≤ p) (hpb : p ≤ (2113/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2672130411/5000000000 : ℝ)*x 0 + (5267275627/10000000000 : ℝ)*x 1 + (-2174901589/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672130411/5000000000 : ℝ)^2113 ≤ (5467340137773/12500000000000 : ℝ)^1601 := by
    have hnat : (2672130411 : ℕ)^2113*12500000000000^1601 ≤ 5467340137773^1601*5000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672130411 5000000000 5467340137773 12500000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5267275627/10000000000 : ℝ)^2113 ≤ (42909082379161/100000000000000 : ℝ)^1601 := by
    have hnat : (5267275627 : ℕ)^2113*100000000000000^1601 ≤ 42909082379161^1601*10000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267275627 10000000000 42909082379161 100000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2174901589/10000000000 : ℝ)^2113 ≤ (6676098252593/50000000000000 : ℝ)^1601 := by
    have hnat : (2174901589 : ℕ)^2113*50000000000000^1601 ≤ 6676098252593^1601*10000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2174901589 10000000000 6676098252593 50000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2113/512 : ℝ)) 2113 1601 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672130411/5000000000 : ℝ), (5267275627/10000000000 : ℝ), (-2174901589/10000000000 : ℝ)] ![(5467340137773/12500000000000 : ℝ), (42909082379161/100000000000000 : ℝ), (6676098252593/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672130411/5000000000 : ℝ)|^2113 ≤ (5467340137773/12500000000000 : ℝ)^1601
        have hw : |(2672130411/5000000000 : ℝ)|=(2672130411/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5267275627/10000000000 : ℝ)|^2113 ≤ (42909082379161/100000000000000 : ℝ)^1601
        have hw : |(5267275627/10000000000 : ℝ)|=(5267275627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2174901589/10000000000 : ℝ)|^2113 ≤ (6676098252593/50000000000000 : ℝ)^1601
        have hw : |(-2174901589/10000000000 : ℝ)|=(2174901589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1259_s6_3 (p : ℝ) (hpa : (8451/2048 : ℝ) ≤ p) (hpb : p ≤ (2113/512 : ℝ)) (x : Fin 3 → ℝ) :
    (86968769/200000000 : ℝ)*x 0 + (1056062113/2500000000 : ℝ)*x 1 + (139880057/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (86968769/200000000 : ℝ)^2113 ≤ (16658745155599/50000000000000 : ℝ)^1601 := by
    have hnat : (86968769 : ℕ)^2113*50000000000000^1601 ≤ 16658745155599^1601*200000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      86968769 200000000 16658745155599 50000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1056062113/2500000000 : ℝ)^2113 ≤ (16033712294423/50000000000000 : ℝ)^1601 := by
    have hnat : (1056062113 : ℕ)^2113*50000000000000^1601 ≤ 16033712294423^1601*2500000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056062113 2500000000 16033712294423 50000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (139880057/312500000 : ℝ)^2113 ≤ (34615085081961/100000000000000 : ℝ)^1601 := by
    have hnat : (139880057 : ℕ)^2113*100000000000000^1601 ≤ 34615085081961^1601*312500000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      139880057 312500000 34615085081961 100000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2113/512 : ℝ)) 2113 1601 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(86968769/200000000 : ℝ), (1056062113/2500000000 : ℝ), (139880057/312500000 : ℝ)] ![(16658745155599/50000000000000 : ℝ), (16033712294423/50000000000000 : ℝ), (34615085081961/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(86968769/200000000 : ℝ)|^2113 ≤ (16658745155599/50000000000000 : ℝ)^1601
        have hw : |(86968769/200000000 : ℝ)|=(86968769/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1056062113/2500000000 : ℝ)|^2113 ≤ (16033712294423/50000000000000 : ℝ)^1601
        have hw : |(1056062113/2500000000 : ℝ)|=(1056062113/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(139880057/312500000 : ℝ)|^2113 ≤ (34615085081961/100000000000000 : ℝ)^1601
        have hw : |(139880057/312500000 : ℝ)|=(139880057/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1259_s6_4 (p : ℝ) (hpa : (8451/2048 : ℝ) ≤ p) (hpb : p ≤ (2113/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-528037539/2500000000 : ℝ)*x 0 + (5267588557/10000000000 : ℝ)*x 1 + (5390737761/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (528037539/2500000000 : ℝ)^2113 ≤ (200720494849/1562500000000 : ℝ)^1601 := by
    have hnat : (528037539 : ℕ)^2113*1562500000000^1601 ≤ 200720494849^1601*2500000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528037539 2500000000 200720494849 1562500000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5267588557/10000000000 : ℝ)^2113 ≤ (335253491373/781250000000 : ℝ)^1601 := by
    have hnat : (5267588557 : ℕ)^2113*781250000000^1601 ≤ 335253491373^1601*10000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267588557 10000000000 335253491373 781250000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5390737761/10000000000 : ℝ)^2113 ≤ (44241441419993/100000000000000 : ℝ)^1601 := by
    have hnat : (5390737761 : ℕ)^2113*100000000000000^1601 ≤ 44241441419993^1601*10000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390737761 10000000000 44241441419993 100000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2113/512 : ℝ)) 2113 1601 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-528037539/2500000000 : ℝ), (5267588557/10000000000 : ℝ), (5390737761/10000000000 : ℝ)] ![(200720494849/1562500000000 : ℝ), (335253491373/781250000000 : ℝ), (44241441419993/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-528037539/2500000000 : ℝ)|^2113 ≤ (200720494849/1562500000000 : ℝ)^1601
        have hw : |(-528037539/2500000000 : ℝ)|=(528037539/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5267588557/10000000000 : ℝ)|^2113 ≤ (335253491373/781250000000 : ℝ)^1601
        have hw : |(5267588557/10000000000 : ℝ)|=(5267588557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5390737761/10000000000 : ℝ)|^2113 ≤ (44241441419993/100000000000000 : ℝ)^1601
        have hw : |(5390737761/10000000000 : ℝ)|=(5390737761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1259_s6_5 (p : ℝ) (hpa : (8451/2048 : ℝ) ≤ p) (hpb : p ≤ (2113/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2656321497/5000000000 : ℝ)*x 0 + (-51285989/250000000 : ℝ)*x 1 + (67384217/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656321497/5000000000 : ℝ)^2113 ≤ (2169876132951/5000000000000 : ℝ)^1601 := by
    have hnat : (2656321497 : ℕ)^2113*5000000000000^1601 ≤ 2169876132951^1601*5000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656321497 5000000000 2169876132951 5000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (51285989/250000000 : ℝ)^2113 ≤ (247220805187/2000000000000 : ℝ)^1601 := by
    have hnat : (51285989 : ℕ)^2113*2000000000000^1601 ≤ 247220805187^1601*250000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      51285989 250000000 247220805187 2000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (67384217/125000000 : ℝ)^2113 ≤ (8848287415311/20000000000000 : ℝ)^1601 := by
    have hnat : (67384217 : ℕ)^2113*20000000000000^1601 ≤ 8848287415311^1601*125000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67384217 125000000 8848287415311 20000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2113/512 : ℝ)) 2113 1601 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656321497/5000000000 : ℝ), (-51285989/250000000 : ℝ), (67384217/125000000 : ℝ)] ![(2169876132951/5000000000000 : ℝ), (247220805187/2000000000000 : ℝ), (8848287415311/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656321497/5000000000 : ℝ)|^2113 ≤ (2169876132951/5000000000000 : ℝ)^1601
        have hw : |(2656321497/5000000000 : ℝ)|=(2656321497/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-51285989/250000000 : ℝ)|^2113 ≤ (247220805187/2000000000000 : ℝ)^1601
        have hw : |(-51285989/250000000 : ℝ)|=(51285989/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(67384217/125000000 : ℝ)|^2113 ≤ (8848287415311/20000000000000 : ℝ)^1601
        have hw : |(67384217/125000000 : ℝ)|=(67384217/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1259_s6_6 (p : ℝ) (hpa : (8451/2048 : ℝ) ≤ p) (hpb : p ≤ (2113/512 : ℝ)) (x : Fin 3 → ℝ) :
    (664080399/1250000000 : ℝ)*x 0 + (5390737117/10000000000 : ℝ)*x 1 + (-1025719811/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (664080399/1250000000 : ℝ)^2113 ≤ (1735900991747/4000000000000 : ℝ)^1601 := by
    have hnat : (664080399 : ℕ)^2113*4000000000000^1601 ≤ 1735900991747^1601*1250000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      664080399 1250000000 1735900991747 4000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5390737117/10000000000 : ℝ)^2113 ≤ (44241434444497/100000000000000 : ℝ)^1601 := by
    have hnat : (5390737117 : ℕ)^2113*100000000000000^1601 ≤ 44241434444497^1601*10000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390737117 10000000000 44241434444497 100000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1025719811/5000000000 : ℝ)^2113 ≤ (6180520376203/50000000000000 : ℝ)^1601 := by
    have hnat : (1025719811 : ℕ)^2113*50000000000000^1601 ≤ 6180520376203^1601*5000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1025719811 5000000000 6180520376203 50000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2113/512 : ℝ)) 2113 1601 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(664080399/1250000000 : ℝ), (5390737117/10000000000 : ℝ), (-1025719811/5000000000 : ℝ)] ![(1735900991747/4000000000000 : ℝ), (44241434444497/100000000000000 : ℝ), (6180520376203/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(664080399/1250000000 : ℝ)|^2113 ≤ (1735900991747/4000000000000 : ℝ)^1601
        have hw : |(664080399/1250000000 : ℝ)|=(664080399/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5390737117/10000000000 : ℝ)|^2113 ≤ (44241434444497/100000000000000 : ℝ)^1601
        have hw : |(5390737117/10000000000 : ℝ)|=(5390737117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1025719811/5000000000 : ℝ)|^2113 ≤ (6180520376203/50000000000000 : ℝ)^1601
        have hw : |(-1025719811/5000000000 : ℝ)|=(1025719811/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1259_s6_7 (p : ℝ) (hpa : (8451/2048 : ℝ) ≤ p) (hpb : p ≤ (2113/512 : ℝ)) (x : Fin 3 → ℝ) :
    (434844773/1000000000 : ℝ)*x 0 + (4475524631/10000000000 : ℝ)*x 1 + (2112444081/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (434844773/1000000000 : ℝ)^2113 ≤ (33317584152763/100000000000000 : ℝ)^1601 := by
    have hnat : (434844773 : ℕ)^2113*100000000000000^1601 ≤ 33317584152763^1601*1000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      434844773 1000000000 33317584152763 100000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4475524631/10000000000 : ℝ)^2113 ≤ (34608581855167/100000000000000 : ℝ)^1601 := by
    have hnat : (4475524631 : ℕ)^2113*100000000000000^1601 ≤ 34608581855167^1601*10000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4475524631 10000000000 34608581855167 100000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2112444081/5000000000 : ℝ)^2113 ≤ (32073833975169/100000000000000 : ℝ)^1601 := by
    have hnat : (2112444081 : ℕ)^2113*100000000000000^1601 ≤ 32073833975169^1601*5000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2112444081 5000000000 32073833975169 100000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2113/512 : ℝ)) 2113 1601 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(434844773/1000000000 : ℝ), (4475524631/10000000000 : ℝ), (2112444081/5000000000 : ℝ)] ![(33317584152763/100000000000000 : ℝ), (34608581855167/100000000000000 : ℝ), (32073833975169/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(434844773/1000000000 : ℝ)|^2113 ≤ (33317584152763/100000000000000 : ℝ)^1601
        have hw : |(434844773/1000000000 : ℝ)|=(434844773/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4475524631/10000000000 : ℝ)|^2113 ≤ (34608581855167/100000000000000 : ℝ)^1601
        have hw : |(4475524631/10000000000 : ℝ)|=(4475524631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2112444081/5000000000 : ℝ)|^2113 ≤ (32073833975169/100000000000000 : ℝ)^1601
        have hw : |(2112444081/5000000000 : ℝ)|=(2112444081/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1259_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8451/2048 : ℝ) ≤ p) (hpb : p ≤ (2113/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15176157/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14137/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2869/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (2299/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14117/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14137/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2869/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14137/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2869/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14137/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2869/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14137/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2869/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14137/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2869/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14137/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2869/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2869/25000 : ℝ) ^ (8451/2048 : ℝ) ≤ (13190422779874549/100000000000000000000 : ℝ) := by
    have hpowers : (2869/25000 : ℝ)^8451 ≤ (13190422779874549/100000000000000000000 : ℝ)^2048 := by
      have hnat : (2869 : ℕ)^8451*100000000000000000000^2048 ≤ 13190422779874549^2048*25000^8451 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2869 25000 13190422779874549 100000000000000000000 8451 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2869/25000 : ℝ)) (X := (13190422779874549/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8451 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14137/100000 : ℝ) ^ (8451/2048 : ℝ) ≤ (623747892204561/2000000000000000000 : ℝ) := by
    have hpowers : (14137/100000 : ℝ)^8451 ≤ (623747892204561/2000000000000000000 : ℝ)^2048 := by
      have hnat : (14137 : ℕ)^8451*2000000000000000000^2048 ≤ 623747892204561^2048*100000^8451 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14137 100000 623747892204561 2000000000000000000 8451 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14137/100000 : ℝ)) (X := (623747892204561/2000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8451 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013190422779874549/50000000000000000000 : ℝ) ≤ (10000639244740863/10000000000000000 : ℝ) ^ (8451/2048 : ℝ) := by
    have hpowers : (50013190422779874549/50000000000000000000 : ℝ)^2048 ≤ (10000639244740863/10000000000000000 : ℝ)^8451 := by
      have hnat : (50013190422779874549 : ℕ)^2048*10000000000000000^8451 ≤ 10000639244740863^8451*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013190422779874549 50000000000000000000 10000639244740863 10000000000000000 2048 8451 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000639244740863/10000000000000000 : ℝ)) (X := (50013190422779874549/50000000000000000000 : ℝ)) (by norm_num) 8451 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100044377817390102599/100000000000000000000 : ℝ) ≤ (2000215052643601/2000000000000000 : ℝ) ^ (8451/2048 : ℝ) := by
    have hpowers : (100044377817390102599/100000000000000000000 : ℝ)^2048 ≤ (2000215052643601/2000000000000000 : ℝ)^8451 := by
      have hnat : (100044377817390102599 : ℕ)^2048*2000000000000000^8451 ≤ 2000215052643601^8451*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100044377817390102599 100000000000000000000 2000215052643601 2000000000000000 2048 8451 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000215052643601/2000000000000000 : ℝ)) (X := (100044377817390102599/100000000000000000000 : ℝ)) (by norm_num) 8451 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (1000623747892204561/1000000000000000000 : ℝ) ≤ (10001511281695147/10000000000000000 : ℝ) ^ (8451/2048 : ℝ) := by
    have hpowers : (1000623747892204561/1000000000000000000 : ℝ)^2048 ≤ (10001511281695147/10000000000000000 : ℝ)^8451 := by
      have hnat : (1000623747892204561 : ℕ)^2048*10000000000000000^8451 ≤ 10001511281695147^8451*1000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1000623747892204561 1000000000000000000 10001511281695147 10000000000000000 2048 8451 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001511281695147/10000000000000000 : ℝ)) (X := (1000623747892204561/1000000000000000000 : ℝ)) (by norm_num) 8451 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13190422779874549/100000000000000000000 : ℝ) ≤ ((26601693534168073259/26610000000000000000 : ℝ)+2*(218009238571/133050000000000 : ℝ)*(2869/25000 : ℝ))^(8451/2048 : ℝ) := by
    rw [show (26601693534168073259/26610000000000000000 : ℝ)+2*(218009238571/133050000000000 : ℝ)*(2869/25000 : ℝ)=(10000639244740863/10000000000000000 : ℝ) by norm_num, show 1+2*(13190422779874549/100000000000000000000 : ℝ)=(50013190422779874549/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(623747892204561/2000000000000000000 : ℝ)+(13190422779874549/100000000000000000000 : ℝ) ≤ ((26601693534168073259/26610000000000000000 : ℝ)+(218009238571/133050000000000 : ℝ)*((14137/100000 : ℝ)+(2869/25000 : ℝ)))^(8451/2048 : ℝ) := by
    rw [show (26601693534168073259/26610000000000000000 : ℝ)+(218009238571/133050000000000 : ℝ)*((14137/100000 : ℝ)+(2869/25000 : ℝ))=(2000215052643601/2000000000000000 : ℝ) by norm_num, show 1+(623747892204561/2000000000000000000 : ℝ)+(13190422779874549/100000000000000000000 : ℝ)=(100044377817390102599/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(623747892204561/2000000000000000000 : ℝ) ≤ ((26601693534168073259/26610000000000000000 : ℝ)+2*(218009238571/133050000000000 : ℝ)*(14137/100000 : ℝ))^(8451/2048 : ℝ) := by
    rw [show (26601693534168073259/26610000000000000000 : ℝ)+2*(218009238571/133050000000000 : ℝ)*(14137/100000 : ℝ)=(10001511281695147/10000000000000000 : ℝ) by norm_num, show 1+2*(623747892204561/2000000000000000000 : ℝ)=(1000623747892204561/1000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (26601693534168073259/26610000000000000000 : ℝ)*(X 1 0+X 2 0)+(218009238571/133050000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8451/2048 : ℝ)) (lo := (2869/25000 : ℝ)) (hi := (14137/100000 : ℝ)) (c := (26601693534168073259/26610000000000000000 : ℝ)) (alpha := (218009238571/133050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (26601693534168073259/26610000000000000000 : ℝ)*(X 0 1+X 2 1)+(218009238571/133050000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8451/2048 : ℝ)) (lo := (2869/25000 : ℝ)) (hi := (14137/100000 : ℝ)) (c := (26601693534168073259/26610000000000000000 : ℝ)) (alpha := (218009238571/133050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (26601693534168073259/26610000000000000000 : ℝ)*(X 0 2+X 1 2)+(218009238571/133050000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8451/2048 : ℝ)) (lo := (2869/25000 : ℝ)) (hi := (14137/100000 : ℝ)) (c := (26601693534168073259/26610000000000000000 : ℝ)) (alpha := (218009238571/133050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-132009087/625000000 : ℝ)*X 0 0+(2695525953/5000000000 : ℝ)*X 0 1+(329204727/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1259_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((334016301/625000000 : ℝ)*X 1 0+(-543725399/2500000000 : ℝ)*X 1 1+(1316818907/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1259_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672130411/5000000000 : ℝ)*X 2 0+(5267275627/10000000000 : ℝ)*X 2 1+(-2174901589/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1259_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((86968769/200000000 : ℝ)*X 0 0+(1056062113/2500000000 : ℝ)*X 0 1+(139880057/312500000 : ℝ)*X 0 2+(86968769/200000000 : ℝ)*X 1 0+(1056062113/2500000000 : ℝ)*X 1 1+(139880057/312500000 : ℝ)*X 1 2+(86968769/200000000 : ℝ)*X 2 0+(1056062113/2500000000 : ℝ)*X 2 1+(139880057/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1259_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-528037539/2500000000 : ℝ)*X 0 0+(5267588557/10000000000 : ℝ)*X 0 1+(5390737761/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1259_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2656321497/5000000000 : ℝ)*X 1 0+(-51285989/250000000 : ℝ)*X 1 1+(67384217/125000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1259_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((664080399/1250000000 : ℝ)*X 2 0+(5390737117/10000000000 : ℝ)*X 2 1+(-1025719811/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1259_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((434844773/1000000000 : ℝ)*X 0 0+(4475524631/10000000000 : ℝ)*X 0 1+(2112444081/5000000000 : ℝ)*X 0 2+(434844773/1000000000 : ℝ)*X 1 0+(4475524631/10000000000 : ℝ)*X 1 1+(2112444081/5000000000 : ℝ)*X 1 2+(434844773/1000000000 : ℝ)*X 2 0+(4475524631/10000000000 : ℝ)*X 2 1+(2112444081/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1259_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3062213624293467027969581753/443500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (16798341/1250000000000 : ℝ)*(base19) + (1257528521/100000000000000 : ℝ)*(base23) + (10197837/20000000000000 : ℝ)*(lower2) + (34381931/20000000000000 : ℝ)*(upper3) + (114911223/100000000000000 : ℝ)*(upper5) + (6024412393302667/100000000000000 : ℝ)*(major0) + (6024412393302667/100000000000000 : ℝ)*(major1) + (6024412393302667/100000000000000 : ℝ)*(major2) + (8079131145493781/100000000000000 : ℝ)*(sp0) + (4039583565403827/50000000000000 : ℝ)*(sp1) + (8079167217146413/100000000000000 : ℝ)*(sp2) + (3969636406113883/100000000000000 : ℝ)*(sp3) + (37329181153/100000000000000 : ℝ)*(sp4) + (19675661409/100000000000000 : ℝ)*(sp7) + (992414020443823/25000000000000 : ℝ)*(f.failure) + (4039584237337467/50000000000000 : ℝ)*(f.sum) + (26237720744107/6652500000000000000000000000 : ℝ)*base65 + (21562467851534518247/2661000000000000000000000000000000 : ℝ)*base68 + (11889783072587518247/2661000000000000000000000000000000 : ℝ)*base70 + (3676979888763481753/2661000000000000000000000000000000 : ℝ)*base71 + (27020237270641/13305000000000000000000000000 : ℝ)*base74 + (80848516873694518247/2661000000000000000000000000000000 : ℝ)*base76 + (3866853356421481753/2661000000000000000000000000000000 : ℝ)*base77 + (28457952127718518247/2661000000000000000000000000000000 : ℝ)*base80 + (43955495687849/13305000000000000000000000000 : ℝ)*base81 + (28211/250000000000000000000 : ℝ)*base89 + (28211/250000000000000000000 : ℝ)*base91 + (28211/250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (72768990897701807728755989/110875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (568654137/50000000000000 : ℝ)*(base19) + (1765346437/100000000000000 : ℝ)*(base23) + (158900551/100000000000000 : ℝ)*(upper2) + (22745693/50000000000000 : ℝ)*(upper5) + (1513761523639471/25000000000000 : ℝ)*(major0) + (1513761523639471/25000000000000 : ℝ)*(major1) + (1513761523639471/25000000000000 : ℝ)*(major2) + (1885183191/20000000000000 : ℝ)*(sp0) + (6377837929/25000000000000 : ℝ)*(sp1) + (7482701369/25000000000000 : ℝ)*(sp2) + (8120241245509231/100000000000000 : ℝ)*(sp4) + (8120224022765197/100000000000000 : ℝ)*(sp5) + (4060109487636637/50000000000000 : ℝ)*(sp6) + (398984149581339/10000000000000 : ℝ)*(sp7) + (398984149581339/10000000000000 : ℝ)*(f.failure) + (8120250671425187/100000000000000 : ℝ)*(f.sum) + (1392425442637/831562500000000000000000000 : ℝ)*base66 + (3699507241518455989/665250000000000000000000000000000 : ℝ)*base67 + (617250622122455989/665250000000000000000000000000000 : ℝ)*base69 + (3208053458283294011/665250000000000000000000000000000 : ℝ)*base72 + (6147837975079/6652500000000000000000000000 : ℝ)*base73 + (3853999216486794011/665250000000000000000000000000000 : ℝ)*base76 + (4793525027224794011/665250000000000000000000000000000 : ℝ)*base78 + (112917179779794011/665250000000000000000000000000000 : ℝ)*base80 + (2253504900047/3326250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (934223/100000000000000000000 : ℝ)*base89 + (934223/100000000000000000000 : ℝ)*base91 + (934223/100000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1259_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8451/2048 : ℝ) ≤ p) (hpb : p ≤ (2113/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15176157/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14137/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2869/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2299/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14117/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1259_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1259_s7_0 (p : ℝ) (hpa : (8451/2048 : ℝ) ≤ p) (hpb : p ≤ (2113/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1056080567/5000000000 : ℝ)*x 0 + (5390870859/10000000000 : ℝ)*x 1 + (210697851/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1056080567/5000000000 : ℝ)^2113 ≤ (12846199791181/100000000000000 : ℝ)^1601 := by
    have hnat : (1056080567 : ℕ)^2113*100000000000000^1601 ≤ 12846199791181^1601*5000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056080567 5000000000 12846199791181 100000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5390870859/10000000000 : ℝ)^2113 ≤ (22121441539371/50000000000000 : ℝ)^1601 := by
    have hnat : (5390870859 : ℕ)^2113*50000000000000^1601 ≤ 22121441539371^1601*10000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390870859 10000000000 22121441539371 50000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (210697851/400000000 : ℝ)^2113 ≤ (8582183424061/20000000000000 : ℝ)^1601 := by
    have hnat : (210697851 : ℕ)^2113*20000000000000^1601 ≤ 8582183424061^1601*400000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210697851 400000000 8582183424061 20000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2113/512 : ℝ)) 2113 1601 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1056080567/5000000000 : ℝ), (5390870859/10000000000 : ℝ), (210697851/400000000 : ℝ)] ![(12846199791181/100000000000000 : ℝ), (22121441539371/50000000000000 : ℝ), (8582183424061/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1056080567/5000000000 : ℝ)|^2113 ≤ (12846199791181/100000000000000 : ℝ)^1601
        have hw : |(-1056080567/5000000000 : ℝ)|=(1056080567/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5390870859/10000000000 : ℝ)|^2113 ≤ (22121441539371/50000000000000 : ℝ)^1601
        have hw : |(5390870859/10000000000 : ℝ)|=(5390870859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(210697851/400000000 : ℝ)|^2113 ≤ (8582183424061/20000000000000 : ℝ)^1601
        have hw : |(210697851/400000000 : ℝ)|=(210697851/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1259_s7_1 (p : ℝ) (hpa : (8451/2048 : ℝ) ≤ p) (hpb : p ≤ (2113/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1068842951/2000000000 : ℝ)*x 0 + (-2174736547/10000000000 : ℝ)*x 1 + (5267446283/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1068842951/2000000000 : ℝ)^2113 ≤ (4373822350727/10000000000000 : ℝ)^1601 := by
    have hnat : (1068842951 : ℕ)^2113*10000000000000^1601 ≤ 4373822350727^1601*2000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068842951 2000000000 4373822350727 10000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2174736547/10000000000 : ℝ)^2113 ≤ (667542963087/5000000000000 : ℝ)^1601 := by
    have hnat : (2174736547 : ℕ)^2113*5000000000000^1601 ≤ 667542963087^1601*10000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2174736547 10000000000 667542963087 5000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5267446283/10000000000 : ℝ)^2113 ≤ (21455458603159/50000000000000 : ℝ)^1601 := by
    have hnat : (5267446283 : ℕ)^2113*50000000000000^1601 ≤ 21455458603159^1601*10000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267446283 10000000000 21455458603159 50000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2113/512 : ℝ)) 2113 1601 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1068842951/2000000000 : ℝ), (-2174736547/10000000000 : ℝ), (5267446283/10000000000 : ℝ)] ![(4373822350727/10000000000000 : ℝ), (667542963087/5000000000000 : ℝ), (21455458603159/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1068842951/2000000000 : ℝ)|^2113 ≤ (4373822350727/10000000000000 : ℝ)^1601
        have hw : |(1068842951/2000000000 : ℝ)|=(1068842951/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2174736547/10000000000 : ℝ)|^2113 ≤ (667542963087/5000000000000 : ℝ)^1601
        have hw : |(-2174736547/10000000000 : ℝ)|=(2174736547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5267446283/10000000000 : ℝ)|^2113 ≤ (21455458603159/50000000000000 : ℝ)^1601
        have hw : |(5267446283/10000000000 : ℝ)|=(5267446283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1259_s7_2 (p : ℝ) (hpa : (8451/2048 : ℝ) ≤ p) (hpb : p ≤ (2113/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1068842951/2000000000 : ℝ)*x 0 + (1053489257/2000000000 : ℝ)*x 1 + (-1087368273/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1068842951/2000000000 : ℝ)^2113 ≤ (4373822350727/10000000000000 : ℝ)^1601 := by
    have hnat : (1068842951 : ℕ)^2113*10000000000000^1601 ≤ 4373822350727^1601*2000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068842951 2000000000 4373822350727 10000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1053489257/2000000000 : ℝ)^2113 ≤ (42910917227821/100000000000000 : ℝ)^1601 := by
    have hnat : (1053489257 : ℕ)^2113*100000000000000^1601 ≤ 42910917227821^1601*2000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053489257 2000000000 42910917227821 100000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1087368273/5000000000 : ℝ)^2113 ≤ (6675429626819/50000000000000 : ℝ)^1601 := by
    have hnat : (1087368273 : ℕ)^2113*50000000000000^1601 ≤ 6675429626819^1601*5000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1087368273 5000000000 6675429626819 50000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2113/512 : ℝ)) 2113 1601 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1068842951/2000000000 : ℝ), (1053489257/2000000000 : ℝ), (-1087368273/5000000000 : ℝ)] ![(4373822350727/10000000000000 : ℝ), (42910917227821/100000000000000 : ℝ), (6675429626819/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1068842951/2000000000 : ℝ)|^2113 ≤ (4373822350727/10000000000000 : ℝ)^1601
        have hw : |(1068842951/2000000000 : ℝ)|=(1068842951/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1053489257/2000000000 : ℝ)|^2113 ≤ (42910917227821/100000000000000 : ℝ)^1601
        have hw : |(1053489257/2000000000 : ℝ)|=(1053489257/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1087368273/5000000000 : ℝ)|^2113 ≤ (6675429626819/50000000000000 : ℝ)^1601
        have hw : |(-1087368273/5000000000 : ℝ)|=(1087368273/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1259_s7_3 (p : ℝ) (hpa : (8451/2048 : ℝ) ≤ p) (hpb : p ≤ (2113/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2174223667/5000000000 : ℝ)*x 0 + (4224605227/10000000000 : ℝ)*x 1 + (895160557/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2174223667/5000000000 : ℝ)^2113 ≤ (6663516029663/20000000000000 : ℝ)^1601 := by
    have hnat : (2174223667 : ℕ)^2113*20000000000000^1601 ≤ 6663516029663^1601*5000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2174223667 5000000000 6663516029663 20000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4224605227/10000000000 : ℝ)^2113 ≤ (6414199830563/20000000000000 : ℝ)^1601 := by
    have hnat : (4224605227 : ℕ)^2113*20000000000000^1601 ≤ 6414199830563^1601*10000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4224605227 10000000000 6414199830563 20000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (895160557/2000000000 : ℝ)^2113 ≤ (8652855168443/25000000000000 : ℝ)^1601 := by
    have hnat : (895160557 : ℕ)^2113*25000000000000^1601 ≤ 8652855168443^1601*2000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      895160557 2000000000 8652855168443 25000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2113/512 : ℝ)) 2113 1601 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2174223667/5000000000 : ℝ), (4224605227/10000000000 : ℝ), (895160557/2000000000 : ℝ)] ![(6663516029663/20000000000000 : ℝ), (6414199830563/20000000000000 : ℝ), (8652855168443/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2174223667/5000000000 : ℝ)|^2113 ≤ (6663516029663/20000000000000 : ℝ)^1601
        have hw : |(2174223667/5000000000 : ℝ)|=(2174223667/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4224605227/10000000000 : ℝ)|^2113 ≤ (6414199830563/20000000000000 : ℝ)^1601
        have hw : |(4224605227/10000000000 : ℝ)|=(4224605227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(895160557/2000000000 : ℝ)|^2113 ≤ (8652855168443/25000000000000 : ℝ)^1601
        have hw : |(895160557/2000000000 : ℝ)|=(895160557/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1259_s7_4 (p : ℝ) (hpa : (8451/2048 : ℝ) ≤ p) (hpb : p ≤ (2113/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2112165797/10000000000 : ℝ)*x 0 + (5267757599/10000000000 : ℝ)*x 1 + (5390558371/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2112165797/10000000000 : ℝ)^2113 ≤ (12846237221313/100000000000000 : ℝ)^1601 := by
    have hnat : (2112165797 : ℕ)^2113*100000000000000^1601 ≤ 12846237221313^1601*10000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2112165797 10000000000 12846237221313 100000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5267757599/10000000000 : ℝ)^2113 ≤ (42914264404239/100000000000000 : ℝ)^1601 := by
    have hnat : (5267757599 : ℕ)^2113*100000000000000^1601 ≤ 42914264404239^1601*10000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267757599 10000000000 42914264404239 100000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5390558371/10000000000 : ℝ)^2113 ≤ (44239498364757/100000000000000 : ℝ)^1601 := by
    have hnat : (5390558371 : ℕ)^2113*100000000000000^1601 ≤ 44239498364757^1601*10000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390558371 10000000000 44239498364757 100000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2113/512 : ℝ)) 2113 1601 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2112165797/10000000000 : ℝ), (5267757599/10000000000 : ℝ), (5390558371/10000000000 : ℝ)] ![(12846237221313/100000000000000 : ℝ), (42914264404239/100000000000000 : ℝ), (44239498364757/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2112165797/10000000000 : ℝ)|^2113 ≤ (12846237221313/100000000000000 : ℝ)^1601
        have hw : |(-2112165797/10000000000 : ℝ)|=(2112165797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5267757599/10000000000 : ℝ)|^2113 ≤ (42914264404239/100000000000000 : ℝ)^1601
        have hw : |(5267757599/10000000000 : ℝ)|=(5267757599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5390558371/10000000000 : ℝ)|^2113 ≤ (44239498364757/100000000000000 : ℝ)^1601
        have hw : |(5390558371/10000000000 : ℝ)|=(5390558371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1259_s7_5 (p : ℝ) (hpa : (8451/2048 : ℝ) ≤ p) (hpb : p ≤ (2113/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5312686653/10000000000 : ℝ)*x 0 + (-1025812167/5000000000 : ℝ)*x 1 + (5390558239/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312686653/10000000000 : ℝ)^2113 ≤ (4339799335103/10000000000000 : ℝ)^1601 := by
    have hnat : (5312686653 : ℕ)^2113*10000000000000^1601 ≤ 4339799335103^1601*10000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312686653 10000000000 4339799335103 10000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1025812167/5000000000 : ℝ)^2113 ≤ (6181254849197/50000000000000 : ℝ)^1601 := by
    have hnat : (1025812167 : ℕ)^2113*50000000000000^1601 ≤ 6181254849197^1601*5000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1025812167 5000000000 6181254849197 50000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5390558239/10000000000 : ℝ)^2113 ≤ (11059874233753/25000000000000 : ℝ)^1601 := by
    have hnat : (5390558239 : ℕ)^2113*25000000000000^1601 ≤ 11059874233753^1601*10000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390558239 10000000000 11059874233753 25000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2113/512 : ℝ)) 2113 1601 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312686653/10000000000 : ℝ), (-1025812167/5000000000 : ℝ), (5390558239/10000000000 : ℝ)] ![(4339799335103/10000000000000 : ℝ), (6181254849197/50000000000000 : ℝ), (11059874233753/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312686653/10000000000 : ℝ)|^2113 ≤ (4339799335103/10000000000000 : ℝ)^1601
        have hw : |(5312686653/10000000000 : ℝ)|=(5312686653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1025812167/5000000000 : ℝ)|^2113 ≤ (6181254849197/50000000000000 : ℝ)^1601
        have hw : |(-1025812167/5000000000 : ℝ)|=(1025812167/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5390558239/10000000000 : ℝ)|^2113 ≤ (11059874233753/25000000000000 : ℝ)^1601
        have hw : |(5390558239/10000000000 : ℝ)|=(5390558239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1259_s7_6 (p : ℝ) (hpa : (8451/2048 : ℝ) ≤ p) (hpb : p ≤ (2113/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2656343333/5000000000 : ℝ)*x 0 + (5390558141/10000000000 : ℝ)*x 1 + (-41032489/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656343333/5000000000 : ℝ)^2113 ≤ (2712374593199/6250000000000 : ℝ)^1601 := by
    have hnat : (2656343333 : ℕ)^2113*6250000000000^1601 ≤ 2712374593199^1601*5000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656343333 5000000000 2712374593199 6250000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5390558141/10000000000 : ℝ)^2113 ≤ (8847899174707/20000000000000 : ℝ)^1601 := by
    have hnat : (5390558141 : ℕ)^2113*20000000000000^1601 ≤ 8847899174707^1601*10000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390558141 10000000000 8847899174707 20000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (41032489/200000000 : ℝ)^2113 ≤ (772656913807/6250000000000 : ℝ)^1601 := by
    have hnat : (41032489 : ℕ)^2113*6250000000000^1601 ≤ 772656913807^1601*200000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41032489 200000000 772656913807 6250000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2113/512 : ℝ)) 2113 1601 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656343333/5000000000 : ℝ), (5390558141/10000000000 : ℝ), (-41032489/200000000 : ℝ)] ![(2712374593199/6250000000000 : ℝ), (8847899174707/20000000000000 : ℝ), (772656913807/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656343333/5000000000 : ℝ)|^2113 ≤ (2712374593199/6250000000000 : ℝ)^1601
        have hw : |(2656343333/5000000000 : ℝ)|=(2656343333/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5390558141/10000000000 : ℝ)|^2113 ≤ (8847899174707/20000000000000 : ℝ)^1601
        have hw : |(5390558141/10000000000 : ℝ)|=(5390558141/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-41032489/200000000 : ℝ)|^2113 ≤ (772656913807/6250000000000 : ℝ)^1601
        have hw : |(-41032489/200000000 : ℝ)|=(41032489/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1259_s7_7 (p : ℝ) (hpa : (8451/2048 : ℝ) ≤ p) (hpb : p ≤ (2113/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4348456697/10000000000 : ℝ)*x 0 + (4475168903/10000000000 : ℝ)*x 1 + (4225241447/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4348456697/10000000000 : ℝ)^2113 ≤ (16658837414629/50000000000000 : ℝ)^1601 := by
    have hnat : (4348456697 : ℕ)^2113*50000000000000^1601 ≤ 16658837414629^1601*10000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4348456697 10000000000 16658837414629 50000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4475168903/10000000000 : ℝ)^2113 ≤ (34604951404429/100000000000000 : ℝ)^1601 := by
    have hnat : (4475168903 : ℕ)^2113*100000000000000^1601 ≤ 34604951404429^1601*10000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4475168903 10000000000 34604951404429 100000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4225241447/10000000000 : ℝ)^2113 ≤ (32077373743421/100000000000000 : ℝ)^1601 := by
    have hnat : (4225241447 : ℕ)^2113*100000000000000^1601 ≤ 32077373743421^1601*10000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4225241447 10000000000 32077373743421 100000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2113/512 : ℝ)) 2113 1601 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4348456697/10000000000 : ℝ), (4475168903/10000000000 : ℝ), (4225241447/10000000000 : ℝ)] ![(16658837414629/50000000000000 : ℝ), (34604951404429/100000000000000 : ℝ), (32077373743421/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4348456697/10000000000 : ℝ)|^2113 ≤ (16658837414629/50000000000000 : ℝ)^1601
        have hw : |(4348456697/10000000000 : ℝ)|=(4348456697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4475168903/10000000000 : ℝ)|^2113 ≤ (34604951404429/100000000000000 : ℝ)^1601
        have hw : |(4475168903/10000000000 : ℝ)|=(4475168903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4225241447/10000000000 : ℝ)|^2113 ≤ (32077373743421/100000000000000 : ℝ)^1601
        have hw : |(4225241447/10000000000 : ℝ)|=(4225241447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1259_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8451/2048 : ℝ) ≤ p) (hpb : p ≤ (2113/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15176157/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14117/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2299/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (11499/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7057/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14117/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2299/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14117/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2299/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14117/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2299/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14117/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2299/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14117/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2299/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14117/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2299/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2299/20000 : ℝ) ^ (8451/2048 : ℝ) ≤ (13280771874050809/100000000000000000000 : ℝ) := by
    have hpowers : (2299/20000 : ℝ)^8451 ≤ (13280771874050809/100000000000000000000 : ℝ)^2048 := by
      have hnat : (2299 : ℕ)^8451*100000000000000000000^2048 ≤ 13280771874050809^2048*20000^8451 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2299 20000 13280771874050809 100000000000000000000 8451 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2299/20000 : ℝ)) (X := (13280771874050809/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8451 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14117/100000 : ℝ) ^ (8451/2048 : ℝ) ≤ (31005730380895193/100000000000000000000 : ℝ) := by
    have hpowers : (14117/100000 : ℝ)^8451 ≤ (31005730380895193/100000000000000000000 : ℝ)^2048 := by
      have hnat : (14117 : ℕ)^8451*100000000000000000000^2048 ≤ 31005730380895193^2048*100000^8451 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14117 100000 31005730380895193 100000000000000000000 8451 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14117/100000 : ℝ)) (X := (31005730380895193/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8451 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013280771874050809/50000000000000000000 : ℝ) ≤ (10000643622869901/10000000000000000 : ℝ) ^ (8451/2048 : ℝ) := by
    have hpowers : (50013280771874050809/50000000000000000000 : ℝ)^2048 ≤ (10000643622869901/10000000000000000 : ℝ)^8451 := by
      have hnat : (50013280771874050809 : ℕ)^2048*10000000000000000^8451 ≤ 10000643622869901^8451*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013280771874050809 50000000000000000000 10000643622869901 10000000000000000 2048 8451 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000643622869901/10000000000000000 : ℝ)) (X := (50013280771874050809/50000000000000000000 : ℝ)) (by norm_num) 8451 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50022143251127473001/50000000000000000000 : ℝ) ≤ (10001073051046597/10000000000000000 : ℝ) ^ (8451/2048 : ℝ) := by
    have hpowers : (50022143251127473001/50000000000000000000 : ℝ)^2048 ≤ (10001073051046597/10000000000000000 : ℝ)^8451 := by
      have hnat : (50022143251127473001 : ℕ)^2048*10000000000000000^8451 ≤ 10001073051046597^8451*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50022143251127473001 50000000000000000000 10001073051046597 10000000000000000 2048 8451 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001073051046597/10000000000000000 : ℝ)) (X := (50022143251127473001/50000000000000000000 : ℝ)) (by norm_num) 8451 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50031005730380895193/50000000000000000000 : ℝ) ≤ (10001502479223293/10000000000000000 : ℝ) ^ (8451/2048 : ℝ) := by
    have hpowers : (50031005730380895193/50000000000000000000 : ℝ)^2048 ≤ (10001502479223293/10000000000000000 : ℝ)^8451 := by
      have hnat : (50031005730380895193 : ℕ)^2048*10000000000000000^8451 ≤ 10001502479223293^8451*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50031005730380895193 50000000000000000000 10001502479223293 10000000000000000 2048 8451 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001502479223293/10000000000000000 : ℝ)) (X := (50031005730380895193/50000000000000000000 : ℝ)) (by norm_num) 8451 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13280771874050809/100000000000000000000 : ℝ) ≤ ((689784605931122089/690000000000000000 : ℝ)+2*(2825185373/1725000000000 : ℝ)*(2299/20000 : ℝ))^(8451/2048 : ℝ) := by
    rw [show (689784605931122089/690000000000000000 : ℝ)+2*(2825185373/1725000000000 : ℝ)*(2299/20000 : ℝ)=(10000643622869901/10000000000000000 : ℝ) by norm_num, show 1+2*(13280771874050809/100000000000000000000 : ℝ)=(50013280771874050809/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(31005730380895193/100000000000000000000 : ℝ)+(13280771874050809/100000000000000000000 : ℝ) ≤ ((689784605931122089/690000000000000000 : ℝ)+(2825185373/1725000000000 : ℝ)*((14117/100000 : ℝ)+(2299/20000 : ℝ)))^(8451/2048 : ℝ) := by
    rw [show (689784605931122089/690000000000000000 : ℝ)+(2825185373/1725000000000 : ℝ)*((14117/100000 : ℝ)+(2299/20000 : ℝ))=(10001073051046597/10000000000000000 : ℝ) by norm_num, show 1+(31005730380895193/100000000000000000000 : ℝ)+(13280771874050809/100000000000000000000 : ℝ)=(50022143251127473001/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(31005730380895193/100000000000000000000 : ℝ) ≤ ((689784605931122089/690000000000000000 : ℝ)+2*(2825185373/1725000000000 : ℝ)*(14117/100000 : ℝ))^(8451/2048 : ℝ) := by
    rw [show (689784605931122089/690000000000000000 : ℝ)+2*(2825185373/1725000000000 : ℝ)*(14117/100000 : ℝ)=(10001502479223293/10000000000000000 : ℝ) by norm_num, show 1+2*(31005730380895193/100000000000000000000 : ℝ)=(50031005730380895193/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (689784605931122089/690000000000000000 : ℝ)*(X 1 0+X 2 0)+(2825185373/1725000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8451/2048 : ℝ)) (lo := (2299/20000 : ℝ)) (hi := (14117/100000 : ℝ)) (c := (689784605931122089/690000000000000000 : ℝ)) (alpha := (2825185373/1725000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (689784605931122089/690000000000000000 : ℝ)*(X 0 1+X 2 1)+(2825185373/1725000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8451/2048 : ℝ)) (lo := (2299/20000 : ℝ)) (hi := (14117/100000 : ℝ)) (c := (689784605931122089/690000000000000000 : ℝ)) (alpha := (2825185373/1725000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (689784605931122089/690000000000000000 : ℝ)*(X 0 2+X 1 2)+(2825185373/1725000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8451/2048 : ℝ)) (lo := (2299/20000 : ℝ)) (hi := (14117/100000 : ℝ)) (c := (689784605931122089/690000000000000000 : ℝ)) (alpha := (2825185373/1725000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1056080567/5000000000 : ℝ)*X 0 0+(5390870859/10000000000 : ℝ)*X 0 1+(210697851/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1259_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1068842951/2000000000 : ℝ)*X 1 0+(-2174736547/10000000000 : ℝ)*X 1 1+(5267446283/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1259_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1068842951/2000000000 : ℝ)*X 2 0+(1053489257/2000000000 : ℝ)*X 2 1+(-1087368273/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1259_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2174223667/5000000000 : ℝ)*X 0 0+(4224605227/10000000000 : ℝ)*X 0 1+(895160557/2000000000 : ℝ)*X 0 2+(2174223667/5000000000 : ℝ)*X 1 0+(4224605227/10000000000 : ℝ)*X 1 1+(895160557/2000000000 : ℝ)*X 1 2+(2174223667/5000000000 : ℝ)*X 2 0+(4224605227/10000000000 : ℝ)*X 2 1+(895160557/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1259_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2112165797/10000000000 : ℝ)*X 0 0+(5267757599/10000000000 : ℝ)*X 0 1+(5390558371/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1259_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312686653/10000000000 : ℝ)*X 1 0+(-1025812167/5000000000 : ℝ)*X 1 1+(5390558239/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1259_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2656343333/5000000000 : ℝ)*X 2 0+(5390558141/10000000000 : ℝ)*X 2 1+(-41032489/200000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1259_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4348456697/10000000000 : ℝ)*X 0 0+(4475168903/10000000000 : ℝ)*X 0 1+(4225241447/10000000000 : ℝ)*X 0 2+(4348456697/10000000000 : ℝ)*X 1 0+(4475168903/10000000000 : ℝ)*X 1 1+(4225241447/10000000000 : ℝ)*X 1 2+(4348456697/10000000000 : ℝ)*X 2 0+(4475168903/10000000000 : ℝ)*X 2 1+(4225241447/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1259_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (19494642639187461430861737/5750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (69057761/10000000000000 : ℝ)*(base19) + (647623661/100000000000000 : ℝ)*(base23) + (22955513/100000000000000 : ℝ)*(lower2) + (87666921/100000000000000 : ℝ)*(upper3) + (14755779/25000000000000 : ℝ)*(upper5) + (3020776063735233/50000000000000 : ℝ)*(major0) + (3020776063735233/50000000000000 : ℝ)*(major1) + (3020776063735233/50000000000000 : ℝ)*(major2) + (4051067125705609/50000000000000 : ℝ)*(sp0) + (8102153512924147/100000000000000 : ℝ)*(sp1) + (8102153555878097/100000000000000 : ℝ)*(sp2) + (1990469876492419/50000000000000 : ℝ)*(sp3) + (19952090539/100000000000000 : ℝ)*(sp4) + (1018544191/10000000000000 : ℝ)*(sp7) + (995237484606687/25000000000000 : ℝ)*(f.failure) + (8102154203501757/100000000000000 : ℝ)*(f.sum) + (512092561219/115000000000000000000000000 : ℝ)*base65 + (4089395277320579/11500000000000000000000000000000 : ℝ)*base67 + (194263265282679421/11500000000000000000000000000000 : ℝ)*base70 + (3457561004679421/11500000000000000000000000000000 : ℝ)*base72 + (887156415519/115000000000000000000000000 : ℝ)*base73 + (117703781874320579/11500000000000000000000000000000 : ℝ)*base75 + (42276181879679421/11500000000000000000000000000000 : ℝ)*base78 + (47204831225679421/11500000000000000000000000000000 : ℝ)*base80 + (37547987473/57500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (161859/250000000000000000000 : ℝ)*base89 + (161859/250000000000000000000 : ℝ)*base91 + (161859/250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (53783727850093227712856293/5750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2646401779/100000000000000 : ℝ)*(base19) + (260561177/10000000000000 : ℝ)*(base23) + (22479489/20000000000000 : ℝ)*(upper3) + (14007421/100000000000000 : ℝ)*(lower4) + (296673447/100000000000000 : ℝ)*(upper5) + (3036109174948963/50000000000000 : ℝ)*(major0) + (3036109174948963/50000000000000 : ℝ)*(major1) + (3036109174948963/50000000000000 : ℝ)*(major2) + (16244640803/20000000000000 : ℝ)*(sp1) + (16637323901/25000000000000 : ℝ)*(sp2) + (4071639803209551/50000000000000 : ℝ)*(sp4) + (2035798934203327/25000000000000 : ℝ)*(sp5) + (8143210451511727/100000000000000 : ℝ)*(sp6) + (500144597698377/12500000000000 : ℝ)*(sp7) + (500144597698377/12500000000000 : ℝ)*(f.failure) + (4071639803209551/50000000000000 : ℝ)*(f.sum) + (304681877291/172500000000000000000000000 : ℝ)*base65 + (105264960946514569/11500000000000000000000000000000 : ℝ)*base67 + (6810996705485431/11500000000000000000000000000000 : ℝ)*base70 + (152512181314014569/11500000000000000000000000000000 : ℝ)*base71 + (21242767597/345000000000000000000000000 : ℝ)*base73 + (2053078877985431/11500000000000000000000000000000 : ℝ)*base76 + (200509159154514569/11500000000000000000000000000000 : ℝ)*base77 + (97741723633014569/11500000000000000000000000000000 : ℝ)*base79 + (1449262132309/172500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (497189/125000000000000000000 : ℝ)*base89 + (497189/125000000000000000000 : ℝ)*base91 + (497189/125000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1259_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8451/2048 : ℝ) ≤ p) (hpb : p ≤ (2113/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15176157/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14117/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2299/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11499/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7057/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1259_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1259_s8_0 (p : ℝ) (hpa : (8451/2048 : ℝ) ≤ p) (hpb : p ≤ (2113/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1056080217/5000000000 : ℝ)*x 0 + (2695420123/5000000000 : ℝ)*x 1 + (2633738819/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1056080217/5000000000 : ℝ)^2113 ≤ (12846194172249/100000000000000 : ℝ)^1601 := by
    have hnat : (1056080217 : ℕ)^2113*100000000000000^1601 ≤ 12846194172249^1601*5000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056080217 5000000000 12846194172249 100000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2695420123/5000000000 : ℝ)^2113 ≤ (44242551491239/100000000000000 : ℝ)^1601 := by
    have hnat : (2695420123 : ℕ)^2113*100000000000000^1601 ≤ 44242551491239^1601*5000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695420123 5000000000 44242551491239 100000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2633738819/5000000000 : ℝ)^2113 ≤ (4291125432519/10000000000000 : ℝ)^1601 := by
    have hnat : (2633738819 : ℕ)^2113*10000000000000^1601 ≤ 4291125432519^1601*5000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633738819 5000000000 4291125432519 10000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2113/512 : ℝ)) 2113 1601 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1056080217/5000000000 : ℝ), (2695420123/5000000000 : ℝ), (2633738819/5000000000 : ℝ)] ![(12846194172249/100000000000000 : ℝ), (44242551491239/100000000000000 : ℝ), (4291125432519/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1056080217/5000000000 : ℝ)|^2113 ≤ (12846194172249/100000000000000 : ℝ)^1601
        have hw : |(-1056080217/5000000000 : ℝ)|=(1056080217/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2695420123/5000000000 : ℝ)|^2113 ≤ (44242551491239/100000000000000 : ℝ)^1601
        have hw : |(2695420123/5000000000 : ℝ)|=(2695420123/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2633738819/5000000000 : ℝ)|^2113 ≤ (4291125432519/10000000000000 : ℝ)^1601
        have hw : |(2633738819/5000000000 : ℝ)|=(2633738819/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1259_s8_1 (p : ℝ) (hpa : (8451/2048 : ℝ) ≤ p) (hpb : p ≤ (2113/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2112166163/10000000000 : ℝ)*x 0 + (526778827/1000000000 : ℝ)*x 1 + (5390527653/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2112166163/10000000000 : ℝ)^2113 ≤ (2569248031843/20000000000000 : ℝ)^1601 := by
    have hnat : (2112166163 : ℕ)^2113*20000000000000^1601 ≤ 2569248031843^1601*10000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2112166163 10000000000 2569248031843 20000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (526778827/1000000000 : ℝ)^2113 ≤ (4291459417519/10000000000000 : ℝ)^1601 := by
    have hnat : (526778827 : ℕ)^2113*10000000000000^1601 ≤ 4291459417519^1601*1000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526778827 1000000000 4291459417519 10000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5390527653/10000000000 : ℝ)^2113 ≤ (22119582823053/50000000000000 : ℝ)^1601 := by
    have hnat : (5390527653 : ℕ)^2113*50000000000000^1601 ≤ 22119582823053^1601*10000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390527653 10000000000 22119582823053 50000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2113/512 : ℝ)) 2113 1601 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2112166163/10000000000 : ℝ), (526778827/1000000000 : ℝ), (5390527653/10000000000 : ℝ)] ![(2569248031843/20000000000000 : ℝ), (4291459417519/10000000000000 : ℝ), (22119582823053/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2112166163/10000000000 : ℝ)|^2113 ≤ (2569248031843/20000000000000 : ℝ)^1601
        have hw : |(-2112166163/10000000000 : ℝ)|=(2112166163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(526778827/1000000000 : ℝ)|^2113 ≤ (4291459417519/10000000000000 : ℝ)^1601
        have hw : |(526778827/1000000000 : ℝ)|=(526778827/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5390527653/10000000000 : ℝ)|^2113 ≤ (22119582823053/50000000000000 : ℝ)^1601
        have hw : |(5390527653/10000000000 : ℝ)|=(5390527653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1259_s8_2 (p : ℝ) (hpa : (8451/2048 : ℝ) ≤ p) (hpb : p ≤ (2113/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2656348173/5000000000 : ℝ)*x 0 + (-2051653013/10000000000 : ℝ)*x 1 + (2695263767/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656348173/5000000000 : ℝ)^2113 ≤ (5424762231549/12500000000000 : ℝ)^1601 := by
    have hnat : (2656348173 : ℕ)^2113*12500000000000^1601 ≤ 5424762231549^1601*5000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656348173 5000000000 5424762231549 12500000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2051653013/10000000000 : ℝ)^2113 ≤ (12362737775631/100000000000000 : ℝ)^1601 := by
    have hnat : (2051653013 : ℕ)^2113*100000000000000^1601 ≤ 12362737775631^1601*10000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2051653013 10000000000 12362737775631 100000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2695263767/5000000000 : ℝ)^2113 ≤ (11059791089293/25000000000000 : ℝ)^1601 := by
    have hnat : (2695263767 : ℕ)^2113*25000000000000^1601 ≤ 11059791089293^1601*5000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695263767 5000000000 11059791089293 25000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2113/512 : ℝ)) 2113 1601 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656348173/5000000000 : ℝ), (-2051653013/10000000000 : ℝ), (2695263767/5000000000 : ℝ)] ![(5424762231549/12500000000000 : ℝ), (12362737775631/100000000000000 : ℝ), (11059791089293/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656348173/5000000000 : ℝ)|^2113 ≤ (5424762231549/12500000000000 : ℝ)^1601
        have hw : |(2656348173/5000000000 : ℝ)|=(2656348173/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2051653013/10000000000 : ℝ)|^2113 ≤ (12362737775631/100000000000000 : ℝ)^1601
        have hw : |(-2051653013/10000000000 : ℝ)|=(2051653013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2695263767/5000000000 : ℝ)|^2113 ≤ (11059791089293/25000000000000 : ℝ)^1601
        have hw : |(2695263767/5000000000 : ℝ)|=(2695263767/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1259_s8_3 (p : ℝ) (hpa : (8451/2048 : ℝ) ≤ p) (hpb : p ≤ (2113/512 : ℝ)) (x : Fin 3 → ℝ) :
    (66408693/125000000 : ℝ)*x 0 + (1078105577/2000000000 : ℝ)*x 1 + (-2051653763/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (66408693/125000000 : ℝ)^2113 ≤ (21699044042349/50000000000000 : ℝ)^1601 := by
    have hnat : (66408693 : ℕ)^2113*50000000000000^1601 ≤ 21699044042349^1601*125000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66408693 125000000 21699044042349 50000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1078105577/2000000000 : ℝ)^2113 ≤ (22119584079493/50000000000000 : ℝ)^1601 := by
    have hnat : (1078105577 : ℕ)^2113*50000000000000^1601 ≤ 22119584079493^1601*2000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078105577 2000000000 22119584079493 50000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2051653763/10000000000 : ℝ)^2113 ≤ (1545342967527/12500000000000 : ℝ)^1601 := by
    have hnat : (2051653763 : ℕ)^2113*12500000000000^1601 ≤ 1545342967527^1601*10000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2051653763 10000000000 1545342967527 12500000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2113/512 : ℝ)) 2113 1601 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(66408693/125000000 : ℝ), (1078105577/2000000000 : ℝ), (-2051653763/10000000000 : ℝ)] ![(21699044042349/50000000000000 : ℝ), (22119584079493/50000000000000 : ℝ), (1545342967527/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(66408693/125000000 : ℝ)|^2113 ≤ (21699044042349/50000000000000 : ℝ)^1601
        have hw : |(66408693/125000000 : ℝ)|=(66408693/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1078105577/2000000000 : ℝ)|^2113 ≤ (22119584079493/50000000000000 : ℝ)^1601
        have hw : |(1078105577/2000000000 : ℝ)|=(1078105577/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2051653763/10000000000 : ℝ)|^2113 ≤ (1545342967527/12500000000000 : ℝ)^1601
        have hw : |(-2051653763/10000000000 : ℝ)|=(2051653763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1259_s8_4 (p : ℝ) (hpa : (8451/2048 : ℝ) ≤ p) (hpb : p ≤ (2113/512 : ℝ)) (x : Fin 3 → ℝ) :
    (869691871/2000000000 : ℝ)*x 0 + (4475105801/10000000000 : ℝ)*x 1 + (2112651519/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (869691871/2000000000 : ℝ)^2113 ≤ (1041178178363/3125000000000 : ℝ)^1601 := by
    have hnat : (869691871 : ℕ)^2113*3125000000000^1601 ≤ 1041178178363^1601*2000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      869691871 2000000000 1041178178363 3125000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4475105801/10000000000 : ℝ)^2113 ≤ (34604307414431/100000000000000 : ℝ)^1601 := by
    have hnat : (4475105801 : ℕ)^2113*100000000000000^1601 ≤ 34604307414431^1601*10000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4475105801 10000000000 34604307414431 100000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2112651519/5000000000 : ℝ)^2113 ≤ (1283119634769/4000000000000 : ℝ)^1601 := by
    have hnat : (2112651519 : ℕ)^2113*4000000000000^1601 ≤ 1283119634769^1601*5000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2112651519 5000000000 1283119634769 4000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2113/512 : ℝ)) 2113 1601 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(869691871/2000000000 : ℝ), (4475105801/10000000000 : ℝ), (2112651519/5000000000 : ℝ)] ![(1041178178363/3125000000000 : ℝ), (34604307414431/100000000000000 : ℝ), (1283119634769/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(869691871/2000000000 : ℝ)|^2113 ≤ (1041178178363/3125000000000 : ℝ)^1601
        have hw : |(869691871/2000000000 : ℝ)|=(869691871/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4475105801/10000000000 : ℝ)|^2113 ≤ (34604307414431/100000000000000 : ℝ)^1601
        have hw : |(4475105801/10000000000 : ℝ)|=(4475105801/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2112651519/5000000000 : ℝ)|^2113 ≤ (1283119634769/4000000000000 : ℝ)^1601
        have hw : |(2112651519/5000000000 : ℝ)|=(2112651519/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1259_s8_5 (p : ℝ) (hpa : (8451/2048 : ℝ) ≤ p) (hpb : p ≤ (2113/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-751937/200000000 : ℝ)*x 0 + (2903545809/5000000000 : ℝ)*x 1 + (3007758473/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (751937/200000000 : ℝ)^2113 ≤ (315249639/500000000000 : ℝ)^1601 := by
    have hnat : (751937 : ℕ)^2113*500000000000^1601 ≤ 315249639^1601*200000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      751937 200000000 315249639 500000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2903545809/5000000000 : ℝ)^2113 ≤ (24402967299857/50000000000000 : ℝ)^1601 := by
    have hnat : (2903545809 : ℕ)^2113*50000000000000^1601 ≤ 24402967299857^1601*5000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2903545809 5000000000 24402967299857 50000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3007758473/5000000000 : ℝ)^2113 ≤ (25565507728283/50000000000000 : ℝ)^1601 := by
    have hnat : (3007758473 : ℕ)^2113*50000000000000^1601 ≤ 25565507728283^1601*5000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3007758473 5000000000 25565507728283 50000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2113/512 : ℝ)) 2113 1601 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-751937/200000000 : ℝ), (2903545809/5000000000 : ℝ), (3007758473/5000000000 : ℝ)] ![(315249639/500000000000 : ℝ), (24402967299857/50000000000000 : ℝ), (25565507728283/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-751937/200000000 : ℝ)|^2113 ≤ (315249639/500000000000 : ℝ)^1601
        have hw : |(-751937/200000000 : ℝ)|=(751937/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2903545809/5000000000 : ℝ)|^2113 ≤ (24402967299857/50000000000000 : ℝ)^1601
        have hw : |(2903545809/5000000000 : ℝ)|=(2903545809/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3007758473/5000000000 : ℝ)|^2113 ≤ (25565507728283/50000000000000 : ℝ)^1601
        have hw : |(3007758473/5000000000 : ℝ)|=(3007758473/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1259_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8451/2048 : ℝ) ≤ p) (hpb : p ≤ (2113/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15176157/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7057/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11499/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11499/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14113/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7057/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11499/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7057/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11499/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7057/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11499/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7057/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11499/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7057/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11499/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7057/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11499/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11499/100000 : ℝ) ^ (8451/2048 : ℝ) ≤ (1329985232870237/10000000000000000000 : ℝ) := by
    have hpowers : (11499/100000 : ℝ)^8451 ≤ (1329985232870237/10000000000000000000 : ℝ)^2048 := by
      have hnat : (11499 : ℕ)^8451*10000000000000000000^2048 ≤ 1329985232870237^2048*100000^8451 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11499 100000 1329985232870237 10000000000000000000 8451 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11499/100000 : ℝ)) (X := (1329985232870237/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8451 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (7057/50000 : ℝ) ^ (8451/2048 : ℝ) ≤ (15489275026869573/50000000000000000000 : ℝ) := by
    have hpowers : (7057/50000 : ℝ)^8451 ≤ (15489275026869573/50000000000000000000 : ℝ)^2048 := by
      have hnat : (7057 : ℕ)^8451*50000000000000000000^2048 ≤ 15489275026869573^2048*50000^8451 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7057 50000 15489275026869573 50000000000000000000 8451 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7057/50000 : ℝ)) (X := (15489275026869573/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8451 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (5001329985232870237/5000000000000000000 : ℝ) ≤ (40002578189873/40000000000000 : ℝ) ^ (8451/2048 : ℝ) := by
    have hpowers : (5001329985232870237/5000000000000000000 : ℝ)^2048 ≤ (40002578189873/40000000000000 : ℝ)^8451 := by
      have hnat : (5001329985232870237 : ℕ)^2048*40000000000000^8451 ≤ 40002578189873^8451*5000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5001329985232870237 5000000000000000000 40002578189873 40000000000000 2048 8451 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (40002578189873/40000000000000 : ℝ)) (X := (5001329985232870237/5000000000000000000 : ℝ)) (by norm_num) 8451 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (25011069600595610379/25000000000000000000 : ℝ) ≤ (10001072854821589/10000000000000000 : ℝ) ^ (8451/2048 : ℝ) := by
    have hpowers : (25011069600595610379/25000000000000000000 : ℝ)^2048 ≤ (10001072854821589/10000000000000000 : ℝ)^8451 := by
      have hnat : (25011069600595610379 : ℕ)^2048*10000000000000000^8451 ≤ 10001072854821589^8451*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25011069600595610379 25000000000000000000 10001072854821589 10000000000000000 2048 8451 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001072854821589/10000000000000000 : ℝ)) (X := (25011069600595610379/25000000000000000000 : ℝ)) (by norm_num) 8451 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25015489275026869573/25000000000000000000 : ℝ) ≤ (625093822635933/625000000000000 : ℝ) ^ (8451/2048 : ℝ) := by
    have hpowers : (25015489275026869573/25000000000000000000 : ℝ)^2048 ≤ (625093822635933/625000000000000 : ℝ)^8451 := by
      have hnat : (25015489275026869573 : ℕ)^2048*625000000000000^8451 ≤ 625093822635933^8451*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25015489275026869573 25000000000000000000 625093822635933 625000000000000 2048 8451 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625093822635933/625000000000000 : ℝ)) (X := (25015489275026869573/25000000000000000000 : ℝ)) (by norm_num) 8451 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1329985232870237/10000000000000000000 : ℝ) ≤ ((6535458819779345857/6537500000000000000 : ℝ)+2*(428307353339/261500000000000 : ℝ)*(11499/100000 : ℝ))^(8451/2048 : ℝ) := by
    rw [show (6535458819779345857/6537500000000000000 : ℝ)+2*(428307353339/261500000000000 : ℝ)*(11499/100000 : ℝ)=(40002578189873/40000000000000 : ℝ) by norm_num, show 1+2*(1329985232870237/10000000000000000000 : ℝ)=(5001329985232870237/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(15489275026869573/50000000000000000000 : ℝ)+(1329985232870237/10000000000000000000 : ℝ) ≤ ((6535458819779345857/6537500000000000000 : ℝ)+(428307353339/261500000000000 : ℝ)*((7057/50000 : ℝ)+(11499/100000 : ℝ)))^(8451/2048 : ℝ) := by
    rw [show (6535458819779345857/6537500000000000000 : ℝ)+(428307353339/261500000000000 : ℝ)*((7057/50000 : ℝ)+(11499/100000 : ℝ))=(10001072854821589/10000000000000000 : ℝ) by norm_num, show 1+(15489275026869573/50000000000000000000 : ℝ)+(1329985232870237/10000000000000000000 : ℝ)=(25011069600595610379/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(15489275026869573/50000000000000000000 : ℝ) ≤ ((6535458819779345857/6537500000000000000 : ℝ)+2*(428307353339/261500000000000 : ℝ)*(7057/50000 : ℝ))^(8451/2048 : ℝ) := by
    rw [show (6535458819779345857/6537500000000000000 : ℝ)+2*(428307353339/261500000000000 : ℝ)*(7057/50000 : ℝ)=(625093822635933/625000000000000 : ℝ) by norm_num, show 1+2*(15489275026869573/50000000000000000000 : ℝ)=(25015489275026869573/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6535458819779345857/6537500000000000000 : ℝ)*(X 1 0+X 2 0)+(428307353339/261500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8451/2048 : ℝ)) (lo := (11499/100000 : ℝ)) (hi := (7057/50000 : ℝ)) (c := (6535458819779345857/6537500000000000000 : ℝ)) (alpha := (428307353339/261500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6535458819779345857/6537500000000000000 : ℝ)*(X 0 1+X 2 1)+(428307353339/261500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8451/2048 : ℝ)) (lo := (11499/100000 : ℝ)) (hi := (7057/50000 : ℝ)) (c := (6535458819779345857/6537500000000000000 : ℝ)) (alpha := (428307353339/261500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6535458819779345857/6537500000000000000 : ℝ)*(X 0 2+X 1 2)+(428307353339/261500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8451/2048 : ℝ)) (lo := (11499/100000 : ℝ)) (hi := (7057/50000 : ℝ)) (c := (6535458819779345857/6537500000000000000 : ℝ)) (alpha := (428307353339/261500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1056080217/5000000000 : ℝ)*X 0 0+(2695420123/5000000000 : ℝ)*X 0 1+(2633738819/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1259_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((-2112166163/10000000000 : ℝ)*X 0 0+(526778827/1000000000 : ℝ)*X 0 1+(5390527653/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1259_s8_1 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2656348173/5000000000 : ℝ)*X 1 0+(-2051653013/10000000000 : ℝ)*X 1 1+(2695263767/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1259_s8_2 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((66408693/125000000 : ℝ)*X 2 0+(1078105577/2000000000 : ℝ)*X 2 1+(-2051653763/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1259_s8_3 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((869691871/2000000000 : ℝ)*X 0 0+(4475105801/10000000000 : ℝ)*X 0 1+(2112651519/5000000000 : ℝ)*X 0 2+(869691871/2000000000 : ℝ)*X 1 0+(4475105801/10000000000 : ℝ)*X 1 1+(2112651519/5000000000 : ℝ)*X 1 2+(869691871/2000000000 : ℝ)*X 2 0+(4475105801/10000000000 : ℝ)*X 2 1+(2112651519/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1259_s8_4 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((-751937/200000000 : ℝ)*X 0 0+(2903545809/5000000000 : ℝ)*X 0 1+(3007758473/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1259_s8_5 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(lower0) + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (610011116063359076026593639/81718750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (225803317/50000000000000 : ℝ)*(upper1) + (515022569/50000000000000 : ℝ)*(lower2) + (193760843/100000000000000 : ℝ)*(lower3) + (1768197583/100000000000000 : ℝ)*(lower4) + (656987847/100000000000000 : ℝ)*(lower5) + (3037637158195509/50000000000000 : ℝ)*(major0) + (3037637158195509/50000000000000 : ℝ)*(major1) + (3037637158195509/50000000000000 : ℝ)*(major2) + (17164196469/50000000000000 : ℝ)*(sp0) + (101841600969703/1250000000000 : ℝ)*(sp1) + (2036844484857253/25000000000000 : ℝ)*(sp2) + (2036844484857253/25000000000000 : ℝ)*(sp3) + (400317044452757/10000000000000 : ℝ)*(sp4) + (15533459833/100000000000000 : ℝ)*(sp5) + (400317044452757/10000000000000 : ℝ)*(f.failure) + (2036844484857253/25000000000000 : ℝ)*(f.sum) + (89869835958249/6537500000000000000000000000 : ℝ)*base66 + (1580143479711068787/326875000000000000000000000000000 : ℝ)*base68 + (3675370366829818787/326875000000000000000000000000000 : ℝ)*base70 + (5234771571317318787/326875000000000000000000000000000 : ℝ)*base72 + (18365901250987/3268750000000000000000000000 : ℝ)*base74 + (353461669921431213/326875000000000000000000000000000 : ℝ)*base75 + (17289043953782318787/326875000000000000000000000000000 : ℝ)*base78 + (4075746593082318787/326875000000000000000000000000000 : ℝ)*base80 + (38121446777849/6537500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1314849/100000000000000000000 : ℝ)*base89 + (1314849/100000000000000000000 : ℝ)*base91 + (1314849/100000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1259_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8451/2048 : ℝ) ≤ p) (hpb : p ≤ (2113/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15176157/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7057/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11499/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11499/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14113/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1259_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1259_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8451/2048 : ℝ) ≤ p) (hpb : p ≤ (2113/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15176157/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14137/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2869/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11499/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14113/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1259_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1259_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1259_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8451/2048 : ℝ) ≤ p) (hpb : p ≤ (2113/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15176157/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14137/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2869/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11499/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14113/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1259_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
