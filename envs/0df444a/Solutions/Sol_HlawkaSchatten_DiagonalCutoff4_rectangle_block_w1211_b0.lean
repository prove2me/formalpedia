-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1211_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:07:11.213107+00:00
-- url     : https://prove2.me/submissions/3d743594-e42d-438c-bb32-8f413e65a41a

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
theorem support_rectangle_w1211_s0_0 (p : ℝ) (hpa : (8403/2048 : ℝ) ≤ p) (hpb : p ≤ (2101/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-58442597/312500000 : ℝ)*x 0 + (6038519529/10000000000 : ℝ)*x 1 + (119728411/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (58442597/312500000 : ℝ)^2101 ≤ (5448010926001/50000000000000 : ℝ)^1589 := by
    have hnat : (58442597 : ℕ)^2101*50000000000000^1589 ≤ 5448010926001^1589*312500000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      58442597 312500000 5448010926001 50000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6038519529/10000000000 : ℝ)^2101 ≤ (51326652170559/100000000000000 : ℝ)^1589 := by
    have hnat : (6038519529 : ℕ)^2101*100000000000000^1589 ≤ 51326652170559^1589*10000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6038519529 10000000000 51326652170559 100000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (119728411/250000000 : ℝ)^2101 ≤ (18888662982989/50000000000000 : ℝ)^1589 := by
    have hnat : (119728411 : ℕ)^2101*50000000000000^1589 ≤ 18888662982989^1589*250000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      119728411 250000000 18888662982989 50000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2101/512 : ℝ)) 2101 1589 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-58442597/312500000 : ℝ), (6038519529/10000000000 : ℝ), (119728411/250000000 : ℝ)] ![(5448010926001/50000000000000 : ℝ), (51326652170559/100000000000000 : ℝ), (18888662982989/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-58442597/312500000 : ℝ)|^2101 ≤ (5448010926001/50000000000000 : ℝ)^1589
        have hw : |(-58442597/312500000 : ℝ)|=(58442597/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6038519529/10000000000 : ℝ)|^2101 ≤ (51326652170559/100000000000000 : ℝ)^1589
        have hw : |(6038519529/10000000000 : ℝ)|=(6038519529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(119728411/250000000 : ℝ)|^2101 ≤ (18888662982989/50000000000000 : ℝ)^1589
        have hw : |(119728411/250000000 : ℝ)|=(119728411/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1211_s0_1 (p : ℝ) (hpa : (8403/2048 : ℝ) ≤ p) (hpb : p ≤ (2101/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5512906031/10000000000 : ℝ)*x 0 + (-2585250819/10000000000 : ℝ)*x 1 + (149660513/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5512906031/10000000000 : ℝ)^2101 ≤ (45503989786343/100000000000000 : ℝ)^1589 := by
    have hnat : (5512906031 : ℕ)^2101*100000000000000^1589 ≤ 45503989786343^1589*10000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5512906031 10000000000 45503989786343 100000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2585250819/10000000000 : ℝ)^2101 ≤ (16718684486257/100000000000000 : ℝ)^1589 := by
    have hnat : (2585250819 : ℕ)^2101*100000000000000^1589 ≤ 16718684486257^1589*10000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2585250819 10000000000 16718684486257 100000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (149660513/312500000 : ℝ)^2101 ≤ (18888662857831/50000000000000 : ℝ)^1589 := by
    have hnat : (149660513 : ℕ)^2101*50000000000000^1589 ≤ 18888662857831^1589*312500000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      149660513 312500000 18888662857831 50000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2101/512 : ℝ)) 2101 1589 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5512906031/10000000000 : ℝ), (-2585250819/10000000000 : ℝ), (149660513/312500000 : ℝ)] ![(45503989786343/100000000000000 : ℝ), (16718684486257/100000000000000 : ℝ), (18888662857831/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5512906031/10000000000 : ℝ)|^2101 ≤ (45503989786343/100000000000000 : ℝ)^1589
        have hw : |(5512906031/10000000000 : ℝ)|=(5512906031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2585250819/10000000000 : ℝ)|^2101 ≤ (16718684486257/100000000000000 : ℝ)^1589
        have hw : |(-2585250819/10000000000 : ℝ)|=(2585250819/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(149660513/312500000 : ℝ)|^2101 ≤ (18888662857831/50000000000000 : ℝ)^1589
        have hw : |(149660513/312500000 : ℝ)|=(149660513/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1211_s0_2 (p : ℝ) (hpa : (8403/2048 : ℝ) ≤ p) (hpb : p ≤ (2101/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1102581203/2000000000 : ℝ)*x 0 + (4789136433/10000000000 : ℝ)*x 1 + (-1292625409/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1102581203/2000000000 : ℝ)^2101 ≤ (11375997402931/25000000000000 : ℝ)^1589 := by
    have hnat : (1102581203 : ℕ)^2101*25000000000000^1589 ≤ 11375997402931^1589*2000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1102581203 2000000000 11375997402931 25000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4789136433/10000000000 : ℝ)^2101 ≤ (37777325892969/100000000000000 : ℝ)^1589 := by
    have hnat : (4789136433 : ℕ)^2101*100000000000000^1589 ≤ 37777325892969^1589*10000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4789136433 10000000000 37777325892969 100000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1292625409/5000000000 : ℝ)^2101 ≤ (16718684477707/100000000000000 : ℝ)^1589 := by
    have hnat : (1292625409 : ℕ)^2101*100000000000000^1589 ≤ 16718684477707^1589*5000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1292625409 5000000000 16718684477707 100000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2101/512 : ℝ)) 2101 1589 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1102581203/2000000000 : ℝ), (4789136433/10000000000 : ℝ), (-1292625409/5000000000 : ℝ)] ![(11375997402931/25000000000000 : ℝ), (37777325892969/100000000000000 : ℝ), (16718684477707/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1102581203/2000000000 : ℝ)|^2101 ≤ (11375997402931/25000000000000 : ℝ)^1589
        have hw : |(1102581203/2000000000 : ℝ)|=(1102581203/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4789136433/10000000000 : ℝ)|^2101 ≤ (37777325892969/100000000000000 : ℝ)^1589
        have hw : |(4789136433/10000000000 : ℝ)|=(4789136433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1292625409/5000000000 : ℝ)|^2101 ≤ (16718684477707/100000000000000 : ℝ)^1589
        have hw : |(-1292625409/5000000000 : ℝ)|=(1292625409/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1211_s0_3 (p : ℝ) (hpa : (8403/2048 : ℝ) ≤ p) (hpb : p ≤ (2101/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4195467179/10000000000 : ℝ)*x 0 + (3118095313/10000000000 : ℝ)*x 1 + (5637395047/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4195467179/10000000000 : ℝ)^2101 ≤ (31712786568747/100000000000000 : ℝ)^1589 := by
    have hnat : (4195467179 : ℕ)^2101*100000000000000^1589 ≤ 31712786568747^1589*10000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4195467179 10000000000 31712786568747 100000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3118095313/10000000000 : ℝ)^2101 ≤ (21419673117141/100000000000000 : ℝ)^1589 := by
    have hnat : (3118095313 : ℕ)^2101*100000000000000^1589 ≤ 21419673117141^1589*10000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3118095313 10000000000 21419673117141 100000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5637395047/10000000000 : ℝ)^2101 ≤ (23433770148731/50000000000000 : ℝ)^1589 := by
    have hnat : (5637395047 : ℕ)^2101*50000000000000^1589 ≤ 23433770148731^1589*10000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5637395047 10000000000 23433770148731 50000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2101/512 : ℝ)) 2101 1589 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4195467179/10000000000 : ℝ), (3118095313/10000000000 : ℝ), (5637395047/10000000000 : ℝ)] ![(31712786568747/100000000000000 : ℝ), (21419673117141/100000000000000 : ℝ), (23433770148731/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4195467179/10000000000 : ℝ)|^2101 ≤ (31712786568747/100000000000000 : ℝ)^1589
        have hw : |(4195467179/10000000000 : ℝ)|=(4195467179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3118095313/10000000000 : ℝ)|^2101 ≤ (21419673117141/100000000000000 : ℝ)^1589
        have hw : |(3118095313/10000000000 : ℝ)|=(3118095313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5637395047/10000000000 : ℝ)|^2101 ≤ (23433770148731/50000000000000 : ℝ)^1589
        have hw : |(5637395047/10000000000 : ℝ)|=(5637395047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1211_s0_4 (p : ℝ) (hpa : (8403/2048 : ℝ) ≤ p) (hpb : p ≤ (2101/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1875109197/10000000000 : ℝ)*x 0 + (2410665081/5000000000 : ℝ)*x 1 + (6005189093/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1875109197/10000000000 : ℝ)^2101 ≤ (683383783023/6250000000000 : ℝ)^1589 := by
    have hnat : (1875109197 : ℕ)^2101*6250000000000^1589 ≤ 683383783023^1589*10000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1875109197 10000000000 683383783023 6250000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2410665081/5000000000 : ℝ)^2101 ≤ (38113463279497/100000000000000 : ℝ)^1589 := by
    have hnat : (2410665081 : ℕ)^2101*100000000000000^1589 ≤ 38113463279497^1589*5000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2410665081 5000000000 38113463279497 100000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6005189093/10000000000 : ℝ)^2101 ≤ (50952396181459/100000000000000 : ℝ)^1589 := by
    have hnat : (6005189093 : ℕ)^2101*100000000000000^1589 ≤ 50952396181459^1589*10000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6005189093 10000000000 50952396181459 100000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2101/512 : ℝ)) 2101 1589 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1875109197/10000000000 : ℝ), (2410665081/5000000000 : ℝ), (6005189093/10000000000 : ℝ)] ![(683383783023/6250000000000 : ℝ), (38113463279497/100000000000000 : ℝ), (50952396181459/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1875109197/10000000000 : ℝ)|^2101 ≤ (683383783023/6250000000000 : ℝ)^1589
        have hw : |(-1875109197/10000000000 : ℝ)|=(1875109197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2410665081/5000000000 : ℝ)|^2101 ≤ (38113463279497/100000000000000 : ℝ)^1589
        have hw : |(2410665081/5000000000 : ℝ)|=(2410665081/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6005189093/10000000000 : ℝ)|^2101 ≤ (50952396181459/100000000000000 : ℝ)^1589
        have hw : |(6005189093/10000000000 : ℝ)|=(6005189093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1211_s0_5 (p : ℝ) (hpa : (8403/2048 : ℝ) ≤ p) (hpb : p ≤ (2101/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5173101249/10000000000 : ℝ)*x 0 + (-684598283/5000000000 : ℝ)*x 1 + (6005190787/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5173101249/10000000000 : ℝ)^2101 ≤ (8366564819413/20000000000000 : ℝ)^1589 := by
    have hnat : (5173101249 : ℕ)^2101*20000000000000^1589 ≤ 8366564819413^1589*10000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5173101249 10000000000 8366564819413 20000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (684598283/5000000000 : ℝ)^2101 ≤ (3607380350733/50000000000000 : ℝ)^1589 := by
    have hnat : (684598283 : ℕ)^2101*50000000000000^1589 ≤ 3607380350733^1589*5000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      684598283 5000000000 3607380350733 50000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6005190787/10000000000 : ℝ)^2101 ≤ (5095241518583/10000000000000 : ℝ)^1589 := by
    have hnat : (6005190787 : ℕ)^2101*10000000000000^1589 ≤ 5095241518583^1589*10000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6005190787 10000000000 5095241518583 10000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2101/512 : ℝ)) 2101 1589 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5173101249/10000000000 : ℝ), (-684598283/5000000000 : ℝ), (6005190787/10000000000 : ℝ)] ![(8366564819413/20000000000000 : ℝ), (3607380350733/50000000000000 : ℝ), (5095241518583/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5173101249/10000000000 : ℝ)|^2101 ≤ (8366564819413/20000000000000 : ℝ)^1589
        have hw : |(5173101249/10000000000 : ℝ)|=(5173101249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-684598283/5000000000 : ℝ)|^2101 ≤ (3607380350733/50000000000000 : ℝ)^1589
        have hw : |(-684598283/5000000000 : ℝ)|=(684598283/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6005190787/10000000000 : ℝ)|^2101 ≤ (5095241518583/10000000000000 : ℝ)^1589
        have hw : |(6005190787/10000000000 : ℝ)|=(6005190787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1211_s0_6 (p : ℝ) (hpa : (8403/2048 : ℝ) ≤ p) (hpb : p ≤ (2101/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5173102089/10000000000 : ℝ)*x 0 + (6005189581/10000000000 : ℝ)*x 1 + (-68459861/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5173102089/10000000000 : ℝ)^2101 ≤ (2091641653927/5000000000000 : ℝ)^1589 := by
    have hnat : (5173102089 : ℕ)^2101*5000000000000^1589 ≤ 2091641653927^1589*10000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5173102089 10000000000 2091641653927 5000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6005189581/10000000000 : ℝ)^2101 ≤ (50952401656153/100000000000000 : ℝ)^1589 := by
    have hnat : (6005189581 : ℕ)^2101*100000000000000^1589 ≤ 50952401656153^1589*10000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6005189581 10000000000 50952401656153 100000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (68459861/500000000 : ℝ)^2101 ≤ (1442953051603/20000000000000 : ℝ)^1589 := by
    have hnat : (68459861 : ℕ)^2101*20000000000000^1589 ≤ 1442953051603^1589*500000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      68459861 500000000 1442953051603 20000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2101/512 : ℝ)) 2101 1589 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5173102089/10000000000 : ℝ), (6005189581/10000000000 : ℝ), (-68459861/500000000 : ℝ)] ![(2091641653927/5000000000000 : ℝ), (50952401656153/100000000000000 : ℝ), (1442953051603/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5173102089/10000000000 : ℝ)|^2101 ≤ (2091641653927/5000000000000 : ℝ)^1589
        have hw : |(5173102089/10000000000 : ℝ)|=(5173102089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6005189581/10000000000 : ℝ)|^2101 ≤ (50952401656153/100000000000000 : ℝ)^1589
        have hw : |(6005189581/10000000000 : ℝ)|=(6005189581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-68459861/500000000 : ℝ)|^2101 ≤ (1442953051603/20000000000000 : ℝ)^1589
        have hw : |(-68459861/500000000 : ℝ)|=(68459861/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1211_s0_7 (p : ℝ) (hpa : (8403/2048 : ℝ) ≤ p) (hpb : p ≤ (2101/512 : ℝ)) (x : Fin 3 → ℝ) :
    (262839979/625000000 : ℝ)*x 0 + (1114496461/2000000000 : ℝ)*x 1 + (1592649659/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (262839979/625000000 : ℝ)^2101 ≤ (31812493606687/100000000000000 : ℝ)^1589 := by
    have hnat : (262839979 : ℕ)^2101*100000000000000^1589 ≤ 31812493606687^1589*625000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262839979 625000000 31812493606687 100000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1114496461/2000000000 : ℝ)^2101 ≤ (23077657591709/50000000000000 : ℝ)^1589 := by
    have hnat : (1114496461 : ℕ)^2101*50000000000000^1589 ≤ 23077657591709^1589*2000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1114496461 2000000000 23077657591709 50000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1592649659/5000000000 : ℝ)^2101 ≤ (5508047800239/25000000000000 : ℝ)^1589 := by
    have hnat : (1592649659 : ℕ)^2101*25000000000000^1589 ≤ 5508047800239^1589*5000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1592649659 5000000000 5508047800239 25000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2101/512 : ℝ)) 2101 1589 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(262839979/625000000 : ℝ), (1114496461/2000000000 : ℝ), (1592649659/5000000000 : ℝ)] ![(31812493606687/100000000000000 : ℝ), (23077657591709/50000000000000 : ℝ), (5508047800239/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(262839979/625000000 : ℝ)|^2101 ≤ (31812493606687/100000000000000 : ℝ)^1589
        have hw : |(262839979/625000000 : ℝ)|=(262839979/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1114496461/2000000000 : ℝ)|^2101 ≤ (23077657591709/50000000000000 : ℝ)^1589
        have hw : |(1114496461/2000000000 : ℝ)|=(1114496461/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1592649659/5000000000 : ℝ)|^2101 ≤ (5508047800239/25000000000000 : ℝ)^1589
        have hw : |(1592649659/5000000000 : ℝ)|=(1592649659/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1211_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8403/2048 : ℝ) ≤ p) (hpb : p ≤ (2101/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (603287/400000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (347/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (27553/100000 : ℝ)*pair X 0 0 := by
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
  have base1 : ((1 : ℝ)*N 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 0]
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
  have hpowlo : (0 : ℝ) ^ (8403/2048 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^8403 ≤ (0 : ℝ)^2048 := by
      have hnat : (0 : ℕ)^8403*1^2048 ≤ 0^2048*1^8403 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 8403 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 8403 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (8403/2048 : ℝ) ≤ (1164692469769840473/50000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^8403 ≤ (1164692469769840473/50000000000000000000 : ℝ)^2048 := by
      have hnat : (2 : ℕ)^8403*50000000000000000000^2048 ≤ 1164692469769840473^2048*5^8403 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 1164692469769840473 50000000000000000000 8403 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (1164692469769840473/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8403 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (8403/2048 : ℝ) := by
    have hpowers : (1 : ℝ)^2048 ≤ (1 : ℝ)^8403 := by
      have hnat : (1 : ℕ)^2048*1^8403 ≤ 1^8403*1^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 2048 8403 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 8403 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (51164692469769840473/50000000000000000000 : ℝ) ≤ (5028139495465183/5000000000000000 : ℝ) ^ (8403/2048 : ℝ) := by
    have hpowers : (51164692469769840473/50000000000000000000 : ℝ)^2048 ≤ (5028139495465183/5000000000000000 : ℝ)^8403 := by
      have hnat : (51164692469769840473 : ℕ)^2048*5000000000000000^8403 ≤ 5028139495465183^8403*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51164692469769840473 50000000000000000000 5028139495465183 5000000000000000 2048 8403 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5028139495465183/5000000000000000 : ℝ)) (X := (51164692469769840473/50000000000000000000 : ℝ)) (by norm_num) 8403 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (26164692469769840473/25000000000000000000 : ℝ) ≤ (2528139495465183/2500000000000000 : ℝ) ^ (8403/2048 : ℝ) := by
    have hpowers : (26164692469769840473/25000000000000000000 : ℝ)^2048 ≤ (2528139495465183/2500000000000000 : ℝ)^8403 := by
      have hnat : (26164692469769840473 : ℕ)^2048*2500000000000000^8403 ≤ 2528139495465183^8403*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26164692469769840473 25000000000000000000 2528139495465183 2500000000000000 2048 8403 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2528139495465183/2500000000000000 : ℝ)) (X := (26164692469769840473/25000000000000000000 : ℝ)) (by norm_num) 8403 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(28139495465183/2000000000000000 : ℝ)*(0 : ℝ))^(8403/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(28139495465183/2000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1164692469769840473/50000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(28139495465183/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(8403/2048 : ℝ) := by
    rw [show (1 : ℝ)+(28139495465183/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(5028139495465183/5000000000000000 : ℝ) by norm_num, show 1+(1164692469769840473/50000000000000000000 : ℝ)+(0 : ℝ)=(51164692469769840473/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1164692469769840473/50000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(28139495465183/2000000000000000 : ℝ)*(2/5 : ℝ))^(8403/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(28139495465183/2000000000000000 : ℝ)*(2/5 : ℝ)=(2528139495465183/2500000000000000 : ℝ) by norm_num, show 1+2*(1164692469769840473/50000000000000000000 : ℝ)=(26164692469769840473/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(28139495465183/2000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8403/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (28139495465183/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(28139495465183/2000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8403/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (28139495465183/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(28139495465183/2000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8403/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (28139495465183/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-58442597/312500000 : ℝ)*X 0 0+(6038519529/10000000000 : ℝ)*X 0 1+(119728411/250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1211_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5512906031/10000000000 : ℝ)*X 1 0+(-2585250819/10000000000 : ℝ)*X 1 1+(149660513/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1211_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1102581203/2000000000 : ℝ)*X 2 0+(4789136433/10000000000 : ℝ)*X 2 1+(-1292625409/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1211_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4195467179/10000000000 : ℝ)*X 0 0+(3118095313/10000000000 : ℝ)*X 0 1+(5637395047/10000000000 : ℝ)*X 0 2+(4195467179/10000000000 : ℝ)*X 1 0+(3118095313/10000000000 : ℝ)*X 1 1+(5637395047/10000000000 : ℝ)*X 1 2+(4195467179/10000000000 : ℝ)*X 2 0+(3118095313/10000000000 : ℝ)*X 2 1+(5637395047/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1211_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1875109197/10000000000 : ℝ)*X 0 0+(2410665081/5000000000 : ℝ)*X 0 1+(6005189093/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1211_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5173101249/10000000000 : ℝ)*X 1 0+(-684598283/5000000000 : ℝ)*X 1 1+(6005190787/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1211_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5173102089/10000000000 : ℝ)*X 2 0+(6005189581/10000000000 : ℝ)*X 2 1+(-68459861/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1211_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((262839979/625000000 : ℝ)*X 0 0+(1114496461/2000000000 : ℝ)*X 0 1+(1592649659/5000000000 : ℝ)*X 0 2+(262839979/625000000 : ℝ)*X 1 0+(1114496461/2000000000 : ℝ)*X 1 1+(1592649659/5000000000 : ℝ)*X 1 2+(262839979/625000000 : ℝ)*X 2 0+(1114496461/2000000000 : ℝ)*X 2 1+(1592649659/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1211_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (35750145542081313110019/6250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (31624621/50000000000000 : ℝ)*(base1) + (279831939/20000000000000 : ℝ)*(base19) + (1301027193/100000000000000 : ℝ)*(base23) + (11976189/12500000000000 : ℝ)*(base24) + (319982217/100000000000000 : ℝ)*(upper3) + (149667826735469/25000000000000 : ℝ)*(major0) + (149667826735469/25000000000000 : ℝ)*(major1) + (149667826735469/25000000000000 : ℝ)*(major2) + (200099937550241/25000000000000 : ℝ)*(sp0) + (400200693536649/50000000000000 : ℝ)*(sp1) + (12506271709317/1562500000000 : ℝ)*(sp2) + (198468564092499/50000000000000 : ℝ)*(sp3) + (3099281271/100000000000000 : ℝ)*(sp4) + (244554907/10000000000000 : ℝ)*(sp7) + (39693963698331/10000000000000 : ℝ)*(f.failure) + (800402786232993/100000000000000 : ℝ)*(f.sum) + (40254653700827/25000000000000000000000000000 : ℝ)*base65 + (113515311575827/50000000000000000000000000000 : ℝ)*base67 + (255125214225827/50000000000000000000000000000 : ℝ)*base69 + (316454772675827/50000000000000000000000000000 : ℝ)*base71 + (9542300874173/25000000000000000000000000000 : ℝ)*base74 + (37669483975827/50000000000000000000000000000 : ℝ)*base75 + (148924168575827/50000000000000000000000000000 : ℝ)*base77 + (235858369275827/50000000000000000000000000000 : ℝ)*base79 + (111060551125827/25000000000000000000000000000 : ℝ)*base81 + (26003/4000000000000000000 : ℝ)*base90 + (26003/4000000000000000000 : ℝ)*base92 + (26003/4000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (182809246450011348738087/25000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1260639/12500000000000 : ℝ)*(base1) + (1982570437/100000000000000 : ℝ)*(base19) + (134025787/6250000000000 : ℝ)*(base23) + (381471411/100000000000000 : ℝ)*(upper3) + (111985843/100000000000000 : ℝ)*(upper5) + (631799246556563/100000000000000 : ℝ)*(major0) + (631799246556563/100000000000000 : ℝ)*(major1) + (631799246556563/100000000000000 : ℝ)*(major2) + (281423713/6250000000000 : ℝ)*(sp1) + (4878551531/100000000000000 : ℝ)*(sp2) + (422346830387309/50000000000000 : ℝ)*(sp4) + (422343582669831/50000000000000 : ℝ)*(sp5) + (844686627725383/100000000000000 : ℝ)*(sp6) + (10472614714821/2500000000000 : ℝ)*(sp7) + (6545384354343/1562500000000 : ℝ)*(f.failure) + (422346825344753/50000000000000 : ℝ)*(f.sum) + (251977794753971/100000000000000000000000000000 : ℝ)*base66 + (318758256553971/200000000000000000000000000000 : ℝ)*base68 + (1514638312153971/200000000000000000000000000000 : ℝ)*base70 + (1741264042553971/200000000000000000000000000000 : ℝ)*base72 + (39930571046029/100000000000000000000000000000 : ℝ)*base73 + (1932833161753971/200000000000000000000000000000 : ℝ)*base76 + (586411355753971/200000000000000000000000000000 : ℝ)*base78 + (529445322553971/200000000000000000000000000000 : ℝ)*base80 + (392507943553971/100000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (6691/625000000000000000 : ℝ)*base89 + (6691/625000000000000000 : ℝ)*base91 + (6691/625000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1211_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8403/2048 : ℝ) ≤ p) (hpb : p ≤ (2101/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (603287/400000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (347/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (27553/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1211_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1211_s1_0 (p : ℝ) (hpa : (8403/2048 : ℝ) ≤ p) (hpb : p ≤ (2101/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2069824839/10000000000 : ℝ)*x 0 + (5683468893/10000000000 : ℝ)*x 1 + (5016379887/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2069824839/10000000000 : ℝ)^2101 ≤ (12459969533101/100000000000000 : ℝ)^1589 := by
    have hnat : (2069824839 : ℕ)^2101*100000000000000^1589 ≤ 12459969533101^1589*10000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2069824839 10000000000 12459969533101 100000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5683468893/10000000000 : ℝ)^2101 ≤ (23687335981431/50000000000000 : ℝ)^1589 := by
    have hnat : (5683468893 : ℕ)^2101*50000000000000^1589 ≤ 23687335981431^1589*10000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5683468893 10000000000 23687335981431 50000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5016379887/10000000000 : ℝ)^2101 ≤ (5020669811497/12500000000000 : ℝ)^1589 := by
    have hnat : (5016379887 : ℕ)^2101*12500000000000^1589 ≤ 5020669811497^1589*10000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5016379887 10000000000 5020669811497 12500000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2101/512 : ℝ)) 2101 1589 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2069824839/10000000000 : ℝ), (5683468893/10000000000 : ℝ), (5016379887/10000000000 : ℝ)] ![(12459969533101/100000000000000 : ℝ), (23687335981431/50000000000000 : ℝ), (5020669811497/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2069824839/10000000000 : ℝ)|^2101 ≤ (12459969533101/100000000000000 : ℝ)^1589
        have hw : |(-2069824839/10000000000 : ℝ)|=(2069824839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5683468893/10000000000 : ℝ)|^2101 ≤ (23687335981431/50000000000000 : ℝ)^1589
        have hw : |(5683468893/10000000000 : ℝ)|=(5683468893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5016379887/10000000000 : ℝ)|^2101 ≤ (5020669811497/12500000000000 : ℝ)^1589
        have hw : |(5016379887/10000000000 : ℝ)|=(5016379887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1211_s1_1 (p : ℝ) (hpa : (8403/2048 : ℝ) ≤ p) (hpb : p ≤ (2101/512 : ℝ)) (x : Fin 3 → ℝ) :
    (270767391/500000000 : ℝ)*x 0 + (-607145431/2500000000 : ℝ)*x 1 + (1003276077/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (270767391/500000000 : ℝ)^2101 ≤ (22221159434691/50000000000000 : ℝ)^1589 := by
    have hnat : (270767391 : ℕ)^2101*50000000000000^1589 ≤ 22221159434691^1589*500000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270767391 500000000 22221159434691 50000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (607145431/2500000000 : ℝ)^2101 ≤ (1539231734723/10000000000000 : ℝ)^1589 := by
    have hnat : (607145431 : ℕ)^2101*10000000000000^1589 ≤ 1539231734723^1589*2500000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      607145431 2500000000 1539231734723 10000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1003276077/2000000000 : ℝ)^2101 ≤ (20082681882093/50000000000000 : ℝ)^1589 := by
    have hnat : (1003276077 : ℕ)^2101*50000000000000^1589 ≤ 20082681882093^1589*2000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1003276077 2000000000 20082681882093 50000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2101/512 : ℝ)) 2101 1589 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(270767391/500000000 : ℝ), (-607145431/2500000000 : ℝ), (1003276077/2000000000 : ℝ)] ![(22221159434691/50000000000000 : ℝ), (1539231734723/10000000000000 : ℝ), (20082681882093/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(270767391/500000000 : ℝ)|^2101 ≤ (22221159434691/50000000000000 : ℝ)^1589
        have hw : |(270767391/500000000 : ℝ)|=(270767391/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-607145431/2500000000 : ℝ)|^2101 ≤ (1539231734723/10000000000000 : ℝ)^1589
        have hw : |(-607145431/2500000000 : ℝ)|=(607145431/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1003276077/2000000000 : ℝ)|^2101 ≤ (20082681882093/50000000000000 : ℝ)^1589
        have hw : |(1003276077/2000000000 : ℝ)|=(1003276077/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1211_s1_2 (p : ℝ) (hpa : (8403/2048 : ℝ) ≤ p) (hpb : p ≤ (2101/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5415346513/10000000000 : ℝ)*x 0 + (250819061/500000000 : ℝ)*x 1 + (-2428582361/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5415346513/10000000000 : ℝ)^2101 ≤ (8888460937407/20000000000000 : ℝ)^1589 := by
    have hnat : (5415346513 : ℕ)^2101*20000000000000^1589 ≤ 8888460937407^1589*10000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5415346513 10000000000 8888460937407 20000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (250819061/500000000 : ℝ)^2101 ≤ (20082686302069/50000000000000 : ℝ)^1589 := by
    have hnat : (250819061 : ℕ)^2101*50000000000000^1589 ≤ 20082686302069^1589*500000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      250819061 500000000 20082686302069 50000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2428582361/10000000000 : ℝ)^2101 ≤ (7696161342703/50000000000000 : ℝ)^1589 := by
    have hnat : (2428582361 : ℕ)^2101*50000000000000^1589 ≤ 7696161342703^1589*10000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2428582361 10000000000 7696161342703 50000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2101/512 : ℝ)) 2101 1589 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5415346513/10000000000 : ℝ), (250819061/500000000 : ℝ), (-2428582361/10000000000 : ℝ)] ![(8888460937407/20000000000000 : ℝ), (20082686302069/50000000000000 : ℝ), (7696161342703/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5415346513/10000000000 : ℝ)|^2101 ≤ (8888460937407/20000000000000 : ℝ)^1589
        have hw : |(5415346513/10000000000 : ℝ)|=(5415346513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(250819061/500000000 : ℝ)|^2101 ≤ (20082686302069/50000000000000 : ℝ)^1589
        have hw : |(250819061/500000000 : ℝ)|=(250819061/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2428582361/10000000000 : ℝ)|^2101 ≤ (7696161342703/50000000000000 : ℝ)^1589
        have hw : |(-2428582361/10000000000 : ℝ)|=(2428582361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1211_s1_3 (p : ℝ) (hpa : (8403/2048 : ℝ) ≤ p) (hpb : p ≤ (2101/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2155767921/5000000000 : ℝ)*x 0 + (1844903473/5000000000 : ℝ)*x 1 + (1006989933/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2155767921/5000000000 : ℝ)^2101 ≤ (32877960318493/100000000000000 : ℝ)^1589 := by
    have hnat : (2155767921 : ℕ)^2101*100000000000000^1589 ≤ 32877960318493^1589*5000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2155767921 5000000000 32877960318493 100000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1844903473/5000000000 : ℝ)^2101 ≤ (6689992524259/25000000000000 : ℝ)^1589 := by
    have hnat : (1844903473 : ℕ)^2101*25000000000000^1589 ≤ 6689992524259^1589*5000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1844903473 5000000000 6689992524259 25000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1006989933/2000000000 : ℝ)^2101 ≤ (4036206956773/10000000000000 : ℝ)^1589 := by
    have hnat : (1006989933 : ℕ)^2101*10000000000000^1589 ≤ 4036206956773^1589*2000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1006989933 2000000000 4036206956773 10000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2101/512 : ℝ)) 2101 1589 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2155767921/5000000000 : ℝ), (1844903473/5000000000 : ℝ), (1006989933/2000000000 : ℝ)] ![(32877960318493/100000000000000 : ℝ), (6689992524259/25000000000000 : ℝ), (4036206956773/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2155767921/5000000000 : ℝ)|^2101 ≤ (32877960318493/100000000000000 : ℝ)^1589
        have hw : |(2155767921/5000000000 : ℝ)|=(2155767921/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1844903473/5000000000 : ℝ)|^2101 ≤ (6689992524259/25000000000000 : ℝ)^1589
        have hw : |(1844903473/5000000000 : ℝ)|=(1844903473/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1006989933/2000000000 : ℝ)|^2101 ≤ (4036206956773/10000000000000 : ℝ)^1589
        have hw : |(1006989933/2000000000 : ℝ)|=(1006989933/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1211_s1_4 (p : ℝ) (hpa : (8403/2048 : ℝ) ≤ p) (hpb : p ≤ (2101/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-82821457/400000000 : ℝ)*x 0 + (5025248559/10000000000 : ℝ)*x 1 + (5674431253/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (82821457/400000000 : ℝ)^2101 ≤ (12465633712343/100000000000000 : ℝ)^1589 := by
    have hnat : (82821457 : ℕ)^2101*100000000000000^1589 ≤ 12465633712343^1589*400000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      82821457 400000000 12465633712343 100000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5025248559/10000000000 : ℝ)^2101 ≤ (40259275794591/100000000000000 : ℝ)^1589 := by
    have hnat : (5025248559 : ℕ)^2101*100000000000000^1589 ≤ 40259275794591^1589*10000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5025248559 10000000000 40259275794591 100000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5674431253/10000000000 : ℝ)^2101 ≤ (23637545237991/50000000000000 : ℝ)^1589 := by
    have hnat : (5674431253 : ℕ)^2101*50000000000000^1589 ≤ 23637545237991^1589*10000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5674431253 10000000000 23637545237991 50000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2101/512 : ℝ)) 2101 1589 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-82821457/400000000 : ℝ), (5025248559/10000000000 : ℝ), (5674431253/10000000000 : ℝ)] ![(12465633712343/100000000000000 : ℝ), (40259275794591/100000000000000 : ℝ), (23637545237991/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-82821457/400000000 : ℝ)|^2101 ≤ (12465633712343/100000000000000 : ℝ)^1589
        have hw : |(-82821457/400000000 : ℝ)|=(82821457/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5025248559/10000000000 : ℝ)|^2101 ≤ (40259275794591/100000000000000 : ℝ)^1589
        have hw : |(5025248559/10000000000 : ℝ)|=(5025248559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5674431253/10000000000 : ℝ)|^2101 ≤ (23637545237991/50000000000000 : ℝ)^1589
        have hw : |(5674431253/10000000000 : ℝ)|=(5674431253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1211_s1_5 (p : ℝ) (hpa : (8403/2048 : ℝ) ≤ p) (hpb : p ≤ (2101/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5243738769/10000000000 : ℝ)*x 0 + (-885267133/5000000000 : ℝ)*x 1 + (5674427751/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5243738769/10000000000 : ℝ)^2101 ≤ (1703590129829/4000000000000 : ℝ)^1589 := by
    have hnat : (5243738769 : ℕ)^2101*4000000000000^1589 ≤ 1703590129829^1589*10000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243738769 10000000000 1703590129829 4000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (885267133/5000000000 : ℝ)^2101 ≤ (10135194846017/100000000000000 : ℝ)^1589 := by
    have hnat : (885267133 : ℕ)^2101*100000000000000^1589 ≤ 10135194846017^1589*5000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      885267133 5000000000 10135194846017 100000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5674427751/10000000000 : ℝ)^2101 ≤ (47275051898997/100000000000000 : ℝ)^1589 := by
    have hnat : (5674427751 : ℕ)^2101*100000000000000^1589 ≤ 47275051898997^1589*10000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5674427751 10000000000 47275051898997 100000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2101/512 : ℝ)) 2101 1589 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5243738769/10000000000 : ℝ), (-885267133/5000000000 : ℝ), (5674427751/10000000000 : ℝ)] ![(1703590129829/4000000000000 : ℝ), (10135194846017/100000000000000 : ℝ), (47275051898997/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5243738769/10000000000 : ℝ)|^2101 ≤ (1703590129829/4000000000000 : ℝ)^1589
        have hw : |(5243738769/10000000000 : ℝ)|=(5243738769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-885267133/5000000000 : ℝ)|^2101 ≤ (10135194846017/100000000000000 : ℝ)^1589
        have hw : |(-885267133/5000000000 : ℝ)|=(885267133/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5674427751/10000000000 : ℝ)|^2101 ≤ (47275051898997/100000000000000 : ℝ)^1589
        have hw : |(5674427751/10000000000 : ℝ)|=(5674427751/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1211_s1_6 (p : ℝ) (hpa : (8403/2048 : ℝ) ≤ p) (hpb : p ≤ (2101/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1310934731/2500000000 : ℝ)*x 0 + (1134885639/2000000000 : ℝ)*x 1 + (-8852667/50000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1310934731/2500000000 : ℝ)^2101 ≤ (42589754910279/100000000000000 : ℝ)^1589 := by
    have hnat : (1310934731 : ℕ)^2101*100000000000000^1589 ≤ 42589754910279^1589*2500000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310934731 2500000000 42589754910279 100000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1134885639/2000000000 : ℝ)^2101 ≤ (47275056789967/100000000000000 : ℝ)^1589 := by
    have hnat : (1134885639 : ℕ)^2101*100000000000000^1589 ≤ 47275056789967^1589*2000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1134885639 2000000000 47275056789967 100000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8852667/50000000 : ℝ)^2101 ≤ (10135188291393/100000000000000 : ℝ)^1589 := by
    have hnat : (8852667 : ℕ)^2101*100000000000000^1589 ≤ 10135188291393^1589*50000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8852667 50000000 10135188291393 100000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2101/512 : ℝ)) 2101 1589 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1310934731/2500000000 : ℝ), (1134885639/2000000000 : ℝ), (-8852667/50000000 : ℝ)] ![(42589754910279/100000000000000 : ℝ), (47275056789967/100000000000000 : ℝ), (10135188291393/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1310934731/2500000000 : ℝ)|^2101 ≤ (42589754910279/100000000000000 : ℝ)^1589
        have hw : |(1310934731/2500000000 : ℝ)|=(1310934731/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1134885639/2000000000 : ℝ)|^2101 ≤ (47275056789967/100000000000000 : ℝ)^1589
        have hw : |(1134885639/2000000000 : ℝ)|=(1134885639/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-8852667/50000000 : ℝ)|^2101 ≤ (10135188291393/100000000000000 : ℝ)^1589
        have hw : |(-8852667/50000000 : ℝ)|=(8852667/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1211_s1_7 (p : ℝ) (hpa : (8403/2048 : ℝ) ≤ p) (hpb : p ≤ (2101/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4312975429/10000000000 : ℝ)*x 0 + (5017063419/10000000000 : ℝ)*x 1 + (741607557/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4312975429/10000000000 : ℝ)^2101 ≤ (32892475962109/100000000000000 : ℝ)^1589 := by
    have hnat : (4312975429 : ℕ)^2101*100000000000000^1589 ≤ 32892475962109^1589*10000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4312975429 10000000000 32892475962109 100000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5017063419/10000000000 : ℝ)^2101 ≤ (40172595045347/100000000000000 : ℝ)^1589 := by
    have hnat : (5017063419 : ℕ)^2101*100000000000000^1589 ≤ 40172595045347^1589*10000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5017063419 10000000000 40172595045347 100000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (741607557/2000000000 : ℝ)^2101 ≤ (13467464484819/50000000000000 : ℝ)^1589 := by
    have hnat : (741607557 : ℕ)^2101*50000000000000^1589 ≤ 13467464484819^1589*2000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      741607557 2000000000 13467464484819 50000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2101/512 : ℝ)) 2101 1589 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4312975429/10000000000 : ℝ), (5017063419/10000000000 : ℝ), (741607557/2000000000 : ℝ)] ![(32892475962109/100000000000000 : ℝ), (40172595045347/100000000000000 : ℝ), (13467464484819/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4312975429/10000000000 : ℝ)|^2101 ≤ (32892475962109/100000000000000 : ℝ)^1589
        have hw : |(4312975429/10000000000 : ℝ)|=(4312975429/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5017063419/10000000000 : ℝ)|^2101 ≤ (40172595045347/100000000000000 : ℝ)^1589
        have hw : |(5017063419/10000000000 : ℝ)|=(5017063419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(741607557/2000000000 : ℝ)|^2101 ≤ (13467464484819/50000000000000 : ℝ)^1589
        have hw : |(741607557/2000000000 : ℝ)|=(741607557/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1211_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8403/2048 : ℝ) ≤ p) (hpb : p ≤ (2101/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (603287/400000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27553/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (347/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (6027/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (5033/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (27553/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (347/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (27553/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (347/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (27553/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (347/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (27553/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (347/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (27553/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (347/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (27553/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (347/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (347/50000 : ℝ) ^ (8403/2048 : ℝ) ≤ (27801541557/20000000000000000000 : ℝ) := by
    have hpowers : (347/50000 : ℝ)^8403 ≤ (27801541557/20000000000000000000 : ℝ)^2048 := by
      have hnat : (347 : ℕ)^8403*20000000000000000000^2048 ≤ 27801541557^2048*50000^8403 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        347 50000 27801541557 20000000000000000000 8403 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (347/50000 : ℝ)) (X := (27801541557/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8403 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (27553/100000 : ℝ) ^ (8403/2048 : ℝ) ≤ (504658574769032791/100000000000000000000 : ℝ) := by
    have hpowers : (27553/100000 : ℝ)^8403 ≤ (504658574769032791/100000000000000000000 : ℝ)^2048 := by
      have hnat : (27553 : ℕ)^8403*100000000000000000000^2048 ≤ 504658574769032791^2048*100000^8403 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        27553 100000 504658574769032791 100000000000000000000 8403 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (27553/100000 : ℝ)) (X := (504658574769032791/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8403 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000000027801541557/10000000000000000000 : ℝ) ≤ (10000000006775861/10000000000000000 : ℝ) ^ (8403/2048 : ℝ) := by
    have hpowers : (10000000027801541557/10000000000000000000 : ℝ)^2048 ≤ (10000000006775861/10000000000000000 : ℝ)^8403 := by
      have hnat : (10000000027801541557 : ℕ)^2048*10000000000000000^8403 ≤ 10000000006775861^8403*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000000027801541557 10000000000000000000 10000000006775861 10000000000000000 2048 8403 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000006775861/10000000000000000 : ℝ)) (X := (10000000027801541557/10000000000000000000 : ℝ)) (by norm_num) 8403 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (3140770584805523143/3125000000000000000 : ℝ) ≤ (1251534533106813/1250000000000000 : ℝ) ^ (8403/2048 : ℝ) := by
    have hpowers : (3140770584805523143/3125000000000000000 : ℝ)^2048 ≤ (1251534533106813/1250000000000000 : ℝ)^8403 := by
      have hnat : (3140770584805523143 : ℕ)^2048*1250000000000000^8403 ≤ 1251534533106813^8403*3125000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3140770584805523143 3125000000000000000 1251534533106813 1250000000000000 2048 8403 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1251534533106813/1250000000000000 : ℝ)) (X := (3140770584805523143/3125000000000000000 : ℝ)) (by norm_num) 8403 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50504658574769032791/50000000000000000000 : ℝ) ≤ (10024552522933147/10000000000000000 : ℝ) ^ (8403/2048 : ℝ) := by
    have hpowers : (50504658574769032791/50000000000000000000 : ℝ)^2048 ≤ (10024552522933147/10000000000000000 : ℝ)^8403 := by
      have hnat : (50504658574769032791 : ℕ)^2048*10000000000000000^8403 ≤ 10024552522933147^8403*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50504658574769032791 50000000000000000000 10024552522933147 10000000000000000 2048 8403 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10024552522933147/10000000000000000 : ℝ)) (X := (50504658574769032791/50000000000000000000 : ℝ)) (by norm_num) 8403 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(27801541557/20000000000000000000 : ℝ) ≤ ((53714592147155938823/53718000000000000000 : ℝ)+2*(12276258078643/2685900000000000 : ℝ)*(347/50000 : ℝ))^(8403/2048 : ℝ) := by
    rw [show (53714592147155938823/53718000000000000000 : ℝ)+2*(12276258078643/2685900000000000 : ℝ)*(347/50000 : ℝ)=(10000000006775861/10000000000000000 : ℝ) by norm_num, show 1+2*(27801541557/20000000000000000000 : ℝ)=(10000000027801541557/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(504658574769032791/100000000000000000000 : ℝ)+(27801541557/20000000000000000000 : ℝ) ≤ ((53714592147155938823/53718000000000000000 : ℝ)+(12276258078643/2685900000000000 : ℝ)*((27553/100000 : ℝ)+(347/50000 : ℝ)))^(8403/2048 : ℝ) := by
    rw [show (53714592147155938823/53718000000000000000 : ℝ)+(12276258078643/2685900000000000 : ℝ)*((27553/100000 : ℝ)+(347/50000 : ℝ))=(1251534533106813/1250000000000000 : ℝ) by norm_num, show 1+(504658574769032791/100000000000000000000 : ℝ)+(27801541557/20000000000000000000 : ℝ)=(3140770584805523143/3125000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(504658574769032791/100000000000000000000 : ℝ) ≤ ((53714592147155938823/53718000000000000000 : ℝ)+2*(12276258078643/2685900000000000 : ℝ)*(27553/100000 : ℝ))^(8403/2048 : ℝ) := by
    rw [show (53714592147155938823/53718000000000000000 : ℝ)+2*(12276258078643/2685900000000000 : ℝ)*(27553/100000 : ℝ)=(10024552522933147/10000000000000000 : ℝ) by norm_num, show 1+2*(504658574769032791/100000000000000000000 : ℝ)=(50504658574769032791/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (53714592147155938823/53718000000000000000 : ℝ)*(X 1 0+X 2 0)+(12276258078643/2685900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8403/2048 : ℝ)) (lo := (347/50000 : ℝ)) (hi := (27553/100000 : ℝ)) (c := (53714592147155938823/53718000000000000000 : ℝ)) (alpha := (12276258078643/2685900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (53714592147155938823/53718000000000000000 : ℝ)*(X 0 1+X 2 1)+(12276258078643/2685900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8403/2048 : ℝ)) (lo := (347/50000 : ℝ)) (hi := (27553/100000 : ℝ)) (c := (53714592147155938823/53718000000000000000 : ℝ)) (alpha := (12276258078643/2685900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (53714592147155938823/53718000000000000000 : ℝ)*(X 0 2+X 1 2)+(12276258078643/2685900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8403/2048 : ℝ)) (lo := (347/50000 : ℝ)) (hi := (27553/100000 : ℝ)) (c := (53714592147155938823/53718000000000000000 : ℝ)) (alpha := (12276258078643/2685900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2069824839/10000000000 : ℝ)*X 0 0+(5683468893/10000000000 : ℝ)*X 0 1+(5016379887/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1211_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((270767391/500000000 : ℝ)*X 1 0+(-607145431/2500000000 : ℝ)*X 1 1+(1003276077/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1211_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5415346513/10000000000 : ℝ)*X 2 0+(250819061/500000000 : ℝ)*X 2 1+(-2428582361/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1211_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2155767921/5000000000 : ℝ)*X 0 0+(1844903473/5000000000 : ℝ)*X 0 1+(1006989933/2000000000 : ℝ)*X 0 2+(2155767921/5000000000 : ℝ)*X 1 0+(1844903473/5000000000 : ℝ)*X 1 1+(1006989933/2000000000 : ℝ)*X 1 2+(2155767921/5000000000 : ℝ)*X 2 0+(1844903473/5000000000 : ℝ)*X 2 1+(1006989933/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1211_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-82821457/400000000 : ℝ)*X 0 0+(5025248559/10000000000 : ℝ)*X 0 1+(5674431253/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1211_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5243738769/10000000000 : ℝ)*X 1 0+(-885267133/5000000000 : ℝ)*X 1 1+(5674427751/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1211_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1310934731/2500000000 : ℝ)*X 2 0+(1134885639/2000000000 : ℝ)*X 2 1+(-8852667/50000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1211_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4312975429/10000000000 : ℝ)*X 0 0+(5017063419/10000000000 : ℝ)*X 0 1+(741607557/2000000000 : ℝ)*X 0 2+(4312975429/10000000000 : ℝ)*X 1 0+(5017063419/10000000000 : ℝ)*X 1 1+(741607557/2000000000 : ℝ)*X 1 2+(4312975429/10000000000 : ℝ)*X 2 0+(5017063419/10000000000 : ℝ)*X 2 1+(741607557/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1211_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (225126599595546033575439957/55956250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (270219091/25000000000000 : ℝ)*(base19) + (160109461/20000000000000 : ℝ)*(base23) + (2587713/4000000000000 : ℝ)*(upper2) + (52524019/20000000000000 : ℝ)*(upper3) + (10286563/50000000000000 : ℝ)*(upper4) + (70077749362203/6250000000000 : ℝ)*(major0) + (70077749362203/6250000000000 : ℝ)*(major1) + (70077749362203/6250000000000 : ℝ)*(major2) + (374764810848599/25000000000000 : ℝ)*(sp0) + (93691468244013/6250000000000 : ℝ)*(sp1) + (1499063772233267/100000000000000 : ℝ)*(sp2) + (185854745060963/25000000000000 : ℝ)*(sp3) + (83271659/1562500000000 : ℝ)*(sp4) + (858491473/20000000000000 : ℝ)*(sp7) + (371711636350609/50000000000000 : ℝ)*(f.failure) + (374766143195143/25000000000000 : ℝ)*(f.sum) + (35859393361863/44765000000000000000000000000 : ℝ)*base65 + (404281872611808477/111912500000000000000000000000000 : ℝ)*base68 + (241096318956033477/111912500000000000000000000000000 : ℝ)*base70 + (387918428627683477/111912500000000000000000000000000 : ℝ)*base72 + (95174477253213/44765000000000000000000000000 : ℝ)*base73 + (599964823329783477/111912500000000000000000000000000 : ℝ)*base76 + (189768552286220977/111912500000000000000000000000000 : ℝ)*base78 + (554580553496608477/111912500000000000000000000000000 : ℝ)*base80 + (127736500479109/22382500000000000000000000000 : ℝ)*base81 + (251783/20000000000000000000 : ℝ)*base89 + (251783/20000000000000000000 : ℝ)*base91 + (251783/20000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1098538809548239888207566741/111912500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (655123631/50000000000000 : ℝ)*(base19) + (384129921/25000000000000 : ℝ)*(base23) + (37893743/6250000000000 : ℝ)*(base32) + (25261603/50000000000000 : ℝ)*(lower4) + (288040503254767/25000000000000 : ℝ)*(major0) + (288040503254767/25000000000000 : ℝ)*(major1) + (288040503254767/25000000000000 : ℝ)*(major2) + (34466221/3125000000000 : ℝ)*(sp0) + (379480013/25000000000000 : ℝ)*(sp1) + (128018881/3125000000000 : ℝ)*(sp2) + (1540399611984953/100000000000000 : ℝ)*(sp4) + (1540397886736711/100000000000000 : ℝ)*(sp5) + (1540395081780149/100000000000000 : ℝ)*(sp6) + (152784475526503/20000000000000 : ℝ)*(sp7) + (763922983932403/100000000000000 : ℝ)*(f.failure) + (61616028596161/4000000000000 : ℝ)*(f.sum) + (343874085001817/67147500000000000000000000000 : ℝ)*base65 + (13797921809844860759/1342950000000000000000000000000000 : ℝ)*base68 + (12678695784192860759/1342950000000000000000000000000000 : ℝ)*base70 + (3590083762763439241/1342950000000000000000000000000000 : ℝ)*base71 + (694129721412521/134295000000000000000000000000 : ℝ)*base74 + (15554496982636460759/1342950000000000000000000000000000 : ℝ)*base76 + (9720520540036910759/1342950000000000000000000000000000 : ℝ)*base78 + (15674849239377260759/1342950000000000000000000000000000 : ℝ)*base80 + (83741116540639/134295000000000000000000000000 : ℝ)*base81 + (408661/40000000000000000000 : ℝ)*base89 + (408661/40000000000000000000 : ℝ)*base91 + (408661/40000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1211_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8403/2048 : ℝ) ≤ p) (hpb : p ≤ (2101/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (603287/400000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27553/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (347/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (6027/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (5033/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1211_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1211_s2_0 (p : ℝ) (hpa : (8403/2048 : ℝ) ≤ p) (hpb : p ≤ (2101/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-423887529/2000000000 : ℝ)*x 0 + (687271591/1250000000 : ℝ)*x 1 + (2585032187/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (423887529/2000000000 : ℝ)^2101 ≤ (12856379212607/100000000000000 : ℝ)^1589 := by
    have hnat : (423887529 : ℕ)^2101*100000000000000^1589 ≤ 12856379212607^1589*2000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      423887529 2000000000 12856379212607 100000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (687271591/1250000000 : ℝ)^2101 ≤ (11335816142497/25000000000000 : ℝ)^1589 := by
    have hnat : (687271591 : ℕ)^2101*25000000000000^1589 ≤ 11335816142497^1589*1250000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      687271591 1250000000 11335816142497 25000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2585032187/5000000000 : ℝ)^2101 ≤ (10450089049351/25000000000000 : ℝ)^1589 := by
    have hnat : (2585032187 : ℕ)^2101*25000000000000^1589 ≤ 10450089049351^1589*5000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2585032187 5000000000 10450089049351 25000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2101/512 : ℝ)) 2101 1589 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-423887529/2000000000 : ℝ), (687271591/1250000000 : ℝ), (2585032187/5000000000 : ℝ)] ![(12856379212607/100000000000000 : ℝ), (11335816142497/25000000000000 : ℝ), (10450089049351/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-423887529/2000000000 : ℝ)|^2101 ≤ (12856379212607/100000000000000 : ℝ)^1589
        have hw : |(-423887529/2000000000 : ℝ)|=(423887529/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(687271591/1250000000 : ℝ)|^2101 ≤ (11335816142497/25000000000000 : ℝ)^1589
        have hw : |(687271591/1250000000 : ℝ)|=(687271591/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2585032187/5000000000 : ℝ)|^2101 ≤ (10450089049351/25000000000000 : ℝ)^1589
        have hw : |(2585032187/5000000000 : ℝ)|=(2585032187/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1211_s2_1 (p : ℝ) (hpa : (8403/2048 : ℝ) ≤ p) (hpb : p ≤ (2101/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5370956837/10000000000 : ℝ)*x 0 + (-2289578117/10000000000 : ℝ)*x 1 + (5170069183/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5370956837/10000000000 : ℝ)^2101 ≤ (8792253317413/20000000000000 : ℝ)^1589 := by
    have hnat : (5370956837 : ℕ)^2101*20000000000000^1589 ≤ 8792253317413^1589*10000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5370956837 10000000000 8792253317413 20000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2289578117/10000000000 : ℝ)^2101 ≤ (3559581447377/25000000000000 : ℝ)^1589 := by
    have hnat : (2289578117 : ℕ)^2101*25000000000000^1589 ≤ 3559581447377^1589*10000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2289578117 10000000000 3559581447377 25000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5170069183/10000000000 : ℝ)^2101 ≤ (20900203803313/50000000000000 : ℝ)^1589 := by
    have hnat : (5170069183 : ℕ)^2101*50000000000000^1589 ≤ 20900203803313^1589*10000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5170069183 10000000000 20900203803313 50000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2101/512 : ℝ)) 2101 1589 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5370956837/10000000000 : ℝ), (-2289578117/10000000000 : ℝ), (5170069183/10000000000 : ℝ)] ![(8792253317413/20000000000000 : ℝ), (3559581447377/25000000000000 : ℝ), (20900203803313/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5370956837/10000000000 : ℝ)|^2101 ≤ (8792253317413/20000000000000 : ℝ)^1589
        have hw : |(5370956837/10000000000 : ℝ)|=(5370956837/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2289578117/10000000000 : ℝ)|^2101 ≤ (3559581447377/25000000000000 : ℝ)^1589
        have hw : |(-2289578117/10000000000 : ℝ)|=(2289578117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5170069183/10000000000 : ℝ)|^2101 ≤ (20900203803313/50000000000000 : ℝ)^1589
        have hw : |(5170069183/10000000000 : ℝ)|=(5170069183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1211_s2_2 (p : ℝ) (hpa : (8403/2048 : ℝ) ≤ p) (hpb : p ≤ (2101/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2685479527/5000000000 : ℝ)*x 0 + (2585033061/5000000000 : ℝ)*x 1 + (-2289579179/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2685479527/5000000000 : ℝ)^2101 ≤ (5495161322521/12500000000000 : ℝ)^1589 := by
    have hnat : (2685479527 : ℕ)^2101*12500000000000^1589 ≤ 5495161322521^1589*5000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2685479527 5000000000 5495161322521 12500000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2585033061/5000000000 : ℝ)^2101 ≤ (4180037488389/10000000000000 : ℝ)^1589 := by
    have hnat : (2585033061 : ℕ)^2101*10000000000000^1589 ≤ 4180037488389^1589*5000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2585033061 5000000000 4180037488389 10000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2289579179/10000000000 : ℝ)^2101 ≤ (14238334521839/100000000000000 : ℝ)^1589 := by
    have hnat : (2289579179 : ℕ)^2101*100000000000000^1589 ≤ 14238334521839^1589*10000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2289579179 10000000000 14238334521839 100000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2101/512 : ℝ)) 2101 1589 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2685479527/5000000000 : ℝ), (2585033061/5000000000 : ℝ), (-2289579179/10000000000 : ℝ)] ![(5495161322521/12500000000000 : ℝ), (4180037488389/10000000000000 : ℝ), (14238334521839/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2685479527/5000000000 : ℝ)|^2101 ≤ (5495161322521/12500000000000 : ℝ)^1589
        have hw : |(2685479527/5000000000 : ℝ)|=(2685479527/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2585033061/5000000000 : ℝ)|^2101 ≤ (4180037488389/10000000000000 : ℝ)^1589
        have hw : |(2585033061/5000000000 : ℝ)|=(2585033061/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2289579179/10000000000 : ℝ)|^2101 ≤ (14238334521839/100000000000000 : ℝ)^1589
        have hw : |(-2289579179/10000000000 : ℝ)|=(2289579179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1211_s2_3 (p : ℝ) (hpa : (8403/2048 : ℝ) ≤ p) (hpb : p ≤ (2101/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4345736419/10000000000 : ℝ)*x 0 + (4027214357/10000000000 : ℝ)*x 1 + (4688820669/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4345736419/10000000000 : ℝ)^2101 ≤ (33223232923433/100000000000000 : ℝ)^1589 := by
    have hnat : (4345736419 : ℕ)^2101*100000000000000^1589 ≤ 33223232923433^1589*10000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4345736419 10000000000 33223232923433 100000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4027214357/10000000000 : ℝ)^2101 ≤ (30042167286819/100000000000000 : ℝ)^1589 := by
    have hnat : (4027214357 : ℕ)^2101*100000000000000^1589 ≤ 30042167286819^1589*10000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4027214357 10000000000 30042167286819 100000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4688820669/10000000000 : ℝ)^2101 ≤ (36734599768821/100000000000000 : ℝ)^1589 := by
    have hnat : (4688820669 : ℕ)^2101*100000000000000^1589 ≤ 36734599768821^1589*10000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4688820669 10000000000 36734599768821 100000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2101/512 : ℝ)) 2101 1589 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4345736419/10000000000 : ℝ), (4027214357/10000000000 : ℝ), (4688820669/10000000000 : ℝ)] ![(33223232923433/100000000000000 : ℝ), (30042167286819/100000000000000 : ℝ), (36734599768821/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4345736419/10000000000 : ℝ)|^2101 ≤ (33223232923433/100000000000000 : ℝ)^1589
        have hw : |(4345736419/10000000000 : ℝ)|=(4345736419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4027214357/10000000000 : ℝ)|^2101 ≤ (30042167286819/100000000000000 : ℝ)^1589
        have hw : |(4027214357/10000000000 : ℝ)|=(4027214357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4688820669/10000000000 : ℝ)|^2101 ≤ (36734599768821/100000000000000 : ℝ)^1589
        have hw : |(4688820669/10000000000 : ℝ)|=(4688820669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1211_s2_4 (p : ℝ) (hpa : (8403/2048 : ℝ) ≤ p) (hpb : p ≤ (2101/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1059760719/5000000000 : ℝ)*x 0 + (5172221527/10000000000 : ℝ)*x 1 + (686999501/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1059760719/5000000000 : ℝ)^2101 ≤ (6428525638349/50000000000000 : ℝ)^1589 := by
    have hnat : (1059760719 : ℕ)^2101*50000000000000^1589 ≤ 6428525638349^1589*5000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1059760719 5000000000 6428525638349 50000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5172221527/10000000000 : ℝ)^2101 ≤ (10455854540833/25000000000000 : ℝ)^1589 := by
    have hnat : (5172221527 : ℕ)^2101*25000000000000^1589 ≤ 10455854540833^1589*10000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5172221527 10000000000 10455854540833 25000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (686999501/1250000000 : ℝ)^2101 ≤ (22659765271699/50000000000000 : ℝ)^1589 := by
    have hnat : (686999501 : ℕ)^2101*50000000000000^1589 ≤ 22659765271699^1589*1250000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      686999501 1250000000 22659765271699 50000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2101/512 : ℝ)) 2101 1589 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1059760719/5000000000 : ℝ), (5172221527/10000000000 : ℝ), (686999501/1250000000 : ℝ)] ![(6428525638349/50000000000000 : ℝ), (10455854540833/25000000000000 : ℝ), (22659765271699/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1059760719/5000000000 : ℝ)|^2101 ≤ (6428525638349/50000000000000 : ℝ)^1589
        have hw : |(-1059760719/5000000000 : ℝ)|=(1059760719/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5172221527/10000000000 : ℝ)|^2101 ≤ (10455854540833/25000000000000 : ℝ)^1589
        have hw : |(5172221527/10000000000 : ℝ)|=(5172221527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(686999501/1250000000 : ℝ)|^2101 ≤ (22659765271699/50000000000000 : ℝ)^1589
        have hw : |(686999501/1250000000 : ℝ)|=(686999501/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1211_s2_5 (p : ℝ) (hpa : (8403/2048 : ℝ) ≤ p) (hpb : p ≤ (2101/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1321833109/2500000000 : ℝ)*x 0 + (-392729919/2000000000 : ℝ)*x 1 + (5495996037/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1321833109/2500000000 : ℝ)^2101 ≤ (10764633516641/25000000000000 : ℝ)^1589 := by
    have hnat : (1321833109 : ℕ)^2101*25000000000000^1589 ≤ 10764633516641^1589*2500000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1321833109 2500000000 10764633516641 25000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (392729919/2000000000 : ℝ)^2101 ≤ (11621935056047/100000000000000 : ℝ)^1589 := by
    have hnat : (392729919 : ℕ)^2101*100000000000000^1589 ≤ 11621935056047^1589*2000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      392729919 2000000000 11621935056047 100000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5495996037/10000000000 : ℝ)^2101 ≤ (45319530859581/100000000000000 : ℝ)^1589 := by
    have hnat : (5495996037 : ℕ)^2101*100000000000000^1589 ≤ 45319530859581^1589*10000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5495996037 10000000000 45319530859581 100000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2101/512 : ℝ)) 2101 1589 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1321833109/2500000000 : ℝ), (-392729919/2000000000 : ℝ), (5495996037/10000000000 : ℝ)] ![(10764633516641/25000000000000 : ℝ), (11621935056047/100000000000000 : ℝ), (45319530859581/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1321833109/2500000000 : ℝ)|^2101 ≤ (10764633516641/25000000000000 : ℝ)^1589
        have hw : |(1321833109/2500000000 : ℝ)|=(1321833109/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-392729919/2000000000 : ℝ)|^2101 ≤ (11621935056047/100000000000000 : ℝ)^1589
        have hw : |(-392729919/2000000000 : ℝ)|=(392729919/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5495996037/10000000000 : ℝ)|^2101 ≤ (45319530859581/100000000000000 : ℝ)^1589
        have hw : |(5495996037/10000000000 : ℝ)|=(5495996037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1211_s2_6 (p : ℝ) (hpa : (8403/2048 : ℝ) ≤ p) (hpb : p ≤ (2101/512 : ℝ)) (x : Fin 3 → ℝ) :
    (660916577/1250000000 : ℝ)*x 0 + (5495996069/10000000000 : ℝ)*x 1 + (-1963649303/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (660916577/1250000000 : ℝ)^2101 ≤ (43058536004759/100000000000000 : ℝ)^1589 := by
    have hnat : (660916577 : ℕ)^2101*100000000000000^1589 ≤ 43058536004759^1589*1250000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      660916577 1250000000 43058536004759 100000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5495996069/10000000000 : ℝ)^2101 ≤ (45319531208473/100000000000000 : ℝ)^1589 := by
    have hnat : (5495996069 : ℕ)^2101*100000000000000^1589 ≤ 45319531208473^1589*10000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5495996069 10000000000 45319531208473 100000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1963649303/10000000000 : ℝ)^2101 ≤ (5810966385489/50000000000000 : ℝ)^1589 := by
    have hnat : (1963649303 : ℕ)^2101*50000000000000^1589 ≤ 5810966385489^1589*10000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1963649303 10000000000 5810966385489 50000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2101/512 : ℝ)) 2101 1589 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(660916577/1250000000 : ℝ), (5495996069/10000000000 : ℝ), (-1963649303/10000000000 : ℝ)] ![(43058536004759/100000000000000 : ℝ), (45319531208473/100000000000000 : ℝ), (5810966385489/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(660916577/1250000000 : ℝ)|^2101 ≤ (43058536004759/100000000000000 : ℝ)^1589
        have hw : |(660916577/1250000000 : ℝ)|=(660916577/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5495996069/10000000000 : ℝ)|^2101 ≤ (45319531208473/100000000000000 : ℝ)^1589
        have hw : |(5495996069/10000000000 : ℝ)|=(5495996069/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1963649303/10000000000 : ℝ)|^2101 ≤ (5810966385489/50000000000000 : ℝ)^1589
        have hw : |(-1963649303/10000000000 : ℝ)|=(1963649303/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1211_s2_7 (p : ℝ) (hpa : (8403/2048 : ℝ) ≤ p) (hpb : p ≤ (2101/512 : ℝ)) (x : Fin 3 → ℝ) :
    (869181573/2000000000 : ℝ)*x 0 + (2342236773/5000000000 : ℝ)*x 1 + (4031602689/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (869181573/2000000000 : ℝ)^2101 ≤ (33224965972193/100000000000000 : ℝ)^1589 := by
    have hnat : (869181573 : ℕ)^2101*100000000000000^1589 ≤ 33224965972193^1589*2000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      869181573 2000000000 33224965972193 100000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2342236773/5000000000 : ℝ)^2101 ≤ (36689575062813/100000000000000 : ℝ)^1589 := by
    have hnat : (2342236773 : ℕ)^2101*100000000000000^1589 ≤ 36689575062813^1589*5000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2342236773 5000000000 36689575062813 100000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4031602689/10000000000 : ℝ)^2101 ≤ (6017091791823/20000000000000 : ℝ)^1589 := by
    have hnat : (4031602689 : ℕ)^2101*20000000000000^1589 ≤ 6017091791823^1589*10000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4031602689 10000000000 6017091791823 20000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2101/512 : ℝ)) 2101 1589 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(869181573/2000000000 : ℝ), (2342236773/5000000000 : ℝ), (4031602689/10000000000 : ℝ)] ![(33224965972193/100000000000000 : ℝ), (36689575062813/100000000000000 : ℝ), (6017091791823/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(869181573/2000000000 : ℝ)|^2101 ≤ (33224965972193/100000000000000 : ℝ)^1589
        have hw : |(869181573/2000000000 : ℝ)|=(869181573/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2342236773/5000000000 : ℝ)|^2101 ≤ (36689575062813/100000000000000 : ℝ)^1589
        have hw : |(2342236773/5000000000 : ℝ)|=(2342236773/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4031602689/10000000000 : ℝ)|^2101 ≤ (6017091791823/20000000000000 : ℝ)^1589
        have hw : |(4031602689/10000000000 : ℝ)|=(4031602689/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1211_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8403/2048 : ℝ) ≤ p) (hpb : p ≤ (2101/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (603287/400000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (5033/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (6027/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (9371/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8153/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (5033/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (6027/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (5033/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (6027/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (5033/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (6027/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (5033/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (6027/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (5033/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (6027/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (5033/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (6027/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (6027/100000 : ℝ) ^ (8403/2048 : ℝ) ≤ (987920123670247/100000000000000000000 : ℝ) := by
    have hpowers : (6027/100000 : ℝ)^8403 ≤ (987920123670247/100000000000000000000 : ℝ)^2048 := by
      have hnat : (6027 : ℕ)^8403*100000000000000000000^2048 ≤ 987920123670247^2048*100000^8403 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6027 100000 987920123670247 100000000000000000000 8403 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6027/100000 : ℝ)) (X := (987920123670247/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8403 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (5033/25000 : ℝ) ^ (8403/2048 : ℝ) ≤ (139260838413063121/100000000000000000000 : ℝ) := by
    have hpowers : (5033/25000 : ℝ)^8403 ≤ (139260838413063121/100000000000000000000 : ℝ)^2048 := by
      have hnat : (5033 : ℕ)^8403*100000000000000000000^2048 ≤ 139260838413063121^2048*25000^8403 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5033 25000 139260838413063121 100000000000000000000 8403 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5033/25000 : ℝ)) (X := (139260838413063121/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8403 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000987920123670247/50000000000000000000 : ℝ) ≤ (10000048155308743/10000000000000000 : ℝ) ^ (8403/2048 : ℝ) := by
    have hpowers : (50000987920123670247/50000000000000000000 : ℝ)^2048 ≤ (10000048155308743/10000000000000000 : ℝ)^8403 := by
      have hnat : (50000987920123670247 : ℕ)^2048*10000000000000000^8403 ≤ 10000048155308743^8403*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000987920123670247 50000000000000000000 10000048155308743 10000000000000000 2048 8403 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000048155308743/10000000000000000 : ℝ)) (X := (50000987920123670247/50000000000000000000 : ℝ)) (by norm_num) 8403 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (12517531094817091671/12500000000000000000 : ℝ) ≤ (5001708183116871/5000000000000000 : ℝ) ^ (8403/2048 : ℝ) := by
    have hpowers : (12517531094817091671/12500000000000000000 : ℝ)^2048 ≤ (5001708183116871/5000000000000000 : ℝ)^8403 := by
      have hnat : (12517531094817091671 : ℕ)^2048*5000000000000000^8403 ≤ 5001708183116871^8403*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12517531094817091671 12500000000000000000 5001708183116871 5000000000000000 2048 8403 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001708183116871/5000000000000000 : ℝ)) (X := (12517531094817091671/12500000000000000000 : ℝ)) (by norm_num) 8403 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50139260838413063121/50000000000000000000 : ℝ) ≤ (10006784577158741/10000000000000000 : ℝ) ^ (8403/2048 : ℝ) := by
    have hpowers : (50139260838413063121/50000000000000000000 : ℝ)^2048 ≤ (10006784577158741/10000000000000000 : ℝ)^8403 := by
      have hnat : (50139260838413063121 : ℕ)^2048*10000000000000000^8403 ≤ 10006784577158741^8403*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50139260838413063121 50000000000000000000 10006784577158741 10000000000000000 2048 8403 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10006784577158741/10000000000000000 : ℝ)) (X := (50139260838413063121/50000000000000000000 : ℝ)) (by norm_num) 8403 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(987920123670247/100000000000000000000 : ℝ) ≤ ((20144296973734268867/20150000000000000000 : ℝ)+2*(3368210924999/1410500000000000 : ℝ)*(6027/100000 : ℝ))^(8403/2048 : ℝ) := by
    rw [show (20144296973734268867/20150000000000000000 : ℝ)+2*(3368210924999/1410500000000000 : ℝ)*(6027/100000 : ℝ)=(10000048155308743/10000000000000000 : ℝ) by norm_num, show 1+2*(987920123670247/100000000000000000000 : ℝ)=(50000987920123670247/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(139260838413063121/100000000000000000000 : ℝ)+(987920123670247/100000000000000000000 : ℝ) ≤ ((20144296973734268867/20150000000000000000 : ℝ)+(3368210924999/1410500000000000 : ℝ)*((5033/25000 : ℝ)+(6027/100000 : ℝ)))^(8403/2048 : ℝ) := by
    rw [show (20144296973734268867/20150000000000000000 : ℝ)+(3368210924999/1410500000000000 : ℝ)*((5033/25000 : ℝ)+(6027/100000 : ℝ))=(5001708183116871/5000000000000000 : ℝ) by norm_num, show 1+(139260838413063121/100000000000000000000 : ℝ)+(987920123670247/100000000000000000000 : ℝ)=(12517531094817091671/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(139260838413063121/100000000000000000000 : ℝ) ≤ ((20144296973734268867/20150000000000000000 : ℝ)+2*(3368210924999/1410500000000000 : ℝ)*(5033/25000 : ℝ))^(8403/2048 : ℝ) := by
    rw [show (20144296973734268867/20150000000000000000 : ℝ)+2*(3368210924999/1410500000000000 : ℝ)*(5033/25000 : ℝ)=(10006784577158741/10000000000000000 : ℝ) by norm_num, show 1+2*(139260838413063121/100000000000000000000 : ℝ)=(50139260838413063121/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (20144296973734268867/20150000000000000000 : ℝ)*(X 1 0+X 2 0)+(3368210924999/1410500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8403/2048 : ℝ)) (lo := (6027/100000 : ℝ)) (hi := (5033/25000 : ℝ)) (c := (20144296973734268867/20150000000000000000 : ℝ)) (alpha := (3368210924999/1410500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (20144296973734268867/20150000000000000000 : ℝ)*(X 0 1+X 2 1)+(3368210924999/1410500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8403/2048 : ℝ)) (lo := (6027/100000 : ℝ)) (hi := (5033/25000 : ℝ)) (c := (20144296973734268867/20150000000000000000 : ℝ)) (alpha := (3368210924999/1410500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (20144296973734268867/20150000000000000000 : ℝ)*(X 0 2+X 1 2)+(3368210924999/1410500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8403/2048 : ℝ)) (lo := (6027/100000 : ℝ)) (hi := (5033/25000 : ℝ)) (c := (20144296973734268867/20150000000000000000 : ℝ)) (alpha := (3368210924999/1410500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-423887529/2000000000 : ℝ)*X 0 0+(687271591/1250000000 : ℝ)*X 0 1+(2585032187/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1211_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5370956837/10000000000 : ℝ)*X 1 0+(-2289578117/10000000000 : ℝ)*X 1 1+(5170069183/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1211_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2685479527/5000000000 : ℝ)*X 2 0+(2585033061/5000000000 : ℝ)*X 2 1+(-2289579179/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1211_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4345736419/10000000000 : ℝ)*X 0 0+(4027214357/10000000000 : ℝ)*X 0 1+(4688820669/10000000000 : ℝ)*X 0 2+(4345736419/10000000000 : ℝ)*X 1 0+(4027214357/10000000000 : ℝ)*X 1 1+(4688820669/10000000000 : ℝ)*X 1 2+(4345736419/10000000000 : ℝ)*X 2 0+(4027214357/10000000000 : ℝ)*X 2 1+(4688820669/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1211_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1059760719/5000000000 : ℝ)*X 0 0+(5172221527/10000000000 : ℝ)*X 0 1+(686999501/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1211_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1321833109/2500000000 : ℝ)*X 1 0+(-392729919/2000000000 : ℝ)*X 1 1+(5495996037/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1211_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((660916577/1250000000 : ℝ)*X 2 0+(5495996069/10000000000 : ℝ)*X 2 1+(-1963649303/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1211_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((869181573/2000000000 : ℝ)*X 0 0+(2342236773/5000000000 : ℝ)*X 0 1+(4031602689/10000000000 : ℝ)*X 0 2+(869181573/2000000000 : ℝ)*X 1 0+(2342236773/5000000000 : ℝ)*X 1 1+(4031602689/10000000000 : ℝ)*X 1 2+(869181573/2000000000 : ℝ)*X 2 0+(2342236773/5000000000 : ℝ)*X 2 1+(4031602689/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1211_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (591950376295935086376289143/141050000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (25563441/2500000000000 : ℝ)*(base19) + (1982336079/100000000000000 : ℝ)*(base23) + (127813/100000000000 : ℝ)*(upper2) + (677429071/100000000000000 : ℝ)*(upper3) + (57603823/20000000000000 : ℝ)*(upper4) + (45593666325049/2000000000000 : ℝ)*(major0) + (45593666325049/2000000000000 : ℝ)*(major1) + (45593666325049/2000000000000 : ℝ)*(major2) + (1523909411567747/50000000000000 : ℝ)*(sp0) + (121914285561909/4000000000000 : ℝ)*(sp1) + (609571235849857/20000000000000 : ℝ)*(sp2) + (1511486126420529/100000000000000 : ℝ)*(sp3) + (3933844987/10000000000000 : ℝ)*(sp4) + (11102303811/50000000000000 : ℝ)*(sp7) + (1511508331028151/100000000000000 : ℝ)*(f.failure) + (761964540396341/25000000000000 : ℝ)*(f.sum) + (20660009242709/2821000000000000000000000000 : ℝ)*base66 + (317977546216953619/282100000000000000000000000000000 : ℝ)*base68 + (980653558208246381/282100000000000000000000000000000 : ℝ)*base69 + (122560365066853619/282100000000000000000000000000000 : ℝ)*base72 + (1864128116769/1410500000000000000000000000 : ℝ)*base74 + (1292042483125653619/282100000000000000000000000000000 : ℝ)*base76 + (1797029957453353619/282100000000000000000000000000000 : ℝ)*base78 + (1716735378682246381/282100000000000000000000000000000 : ℝ)*base79 + (2337887067689/1410500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (132337/40000000000000000000 : ℝ)*base89 + (132337/40000000000000000000 : ℝ)*base91 + (132337/40000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1219054679901901779730230663/201500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (777927221/50000000000000 : ℝ)*(base19) + (1791070009/100000000000000 : ℝ)*(base23) + (1777557/6250000000000 : ℝ)*(upper2) + (208096657/100000000000000 : ℝ)*(upper3) + (61548903/50000000000000 : ℝ)*(upper5) + (462026586734863/20000000000000 : ℝ)*(major0) + (462026586734863/20000000000000 : ℝ)*(major1) + (462026586734863/20000000000000 : ℝ)*(major2) + (7695248827/50000000000000 : ℝ)*(sp1) + (10106450851/50000000000000 : ℝ)*(sp2) + (772142048139847/25000000000000 : ℝ)*(sp4) + (772137811551823/25000000000000 : ℝ)*(sp5) + (3088546188587677/100000000000000 : ℝ)*(sp6) + (306339494625187/20000000000000 : ℝ)*(sp7) + (306339494625187/20000000000000 : ℝ)*(f.failure) + (772142048139847/25000000000000 : ℝ)*(f.sum) + (3484328464441/7052500000000000000000000000 : ℝ)*base65 + (195338101098571547/2821000000000000000000000000000000 : ℝ)*base67 + (2994088259294428453/2821000000000000000000000000000000 : ℝ)*base70 + (3314836427580428453/2821000000000000000000000000000000 : ℝ)*base72 + (46293408769323/14105000000000000000000000000 : ℝ)*base74 + (1686584388083571547/2821000000000000000000000000000000 : ℝ)*base75 + (470137855410428453/2821000000000000000000000000000000 : ℝ)*base78 + (12331695719202428453/2821000000000000000000000000000000 : ℝ)*base80 + (5339267146407/14105000000000000000000000000 : ℝ)*base81 + (10331/8000000000000000000 : ℝ)*base90 + (10331/8000000000000000000 : ℝ)*base92 + (10331/8000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1211_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8403/2048 : ℝ) ≤ p) (hpb : p ≤ (2101/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (603287/400000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (5033/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (6027/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9371/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8153/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1211_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1211_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8403/2048 : ℝ) ≤ p) (hpb : p ≤ (2101/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (603287/400000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9371/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8153/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1211_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1211_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1211_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8403/2048 : ℝ) ≤ p) (hpb : p ≤ (2101/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (603287/400000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9371/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8153/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1211_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
