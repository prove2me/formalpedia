-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1727_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:01:27.588998+00:00
-- url     : https://prove2.me/submissions/34a62f57-1814-4df5-8735-296202915a4b

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
theorem support_rectangle_w1727_s0_0 (p : ℝ) (hpa : (5431/1024 : ℝ) ≤ p) (hpb : p ≤ (5439/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-257601453/2000000000 : ℝ)*x 0 + (566511771/1000000000 : ℝ)*x 1 + (1244340069/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (257601453/2000000000 : ℝ)^5439 ≤ (8007110286379/100000000000000 : ℝ)^4415 := by
    have hnat : (257601453 : ℕ)^5439*100000000000000^4415 ≤ 8007110286379^4415*2000000000^5439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      257601453 2000000000 8007110286379 100000000000000 5439 4415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (566511771/1000000000 : ℝ)^5439 ≤ (12413923704847/25000000000000 : ℝ)^4415 := by
    have hnat : (566511771 : ℕ)^5439*25000000000000^4415 ≤ 12413923704847^4415*1000000000^5439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      566511771 1000000000 12413923704847 25000000000000 5439 4415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1244340069/2500000000 : ℝ)^5439 ≤ (8467438975451/20000000000000 : ℝ)^4415 := by
    have hnat : (1244340069 : ℕ)^5439*20000000000000^4415 ≤ 8467438975451^4415*2500000000^5439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1244340069 2500000000 8467438975451 20000000000000 5439 4415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5439/1024 : ℝ)) 5439 4415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-257601453/2000000000 : ℝ), (566511771/1000000000 : ℝ), (1244340069/2500000000 : ℝ)] ![(8007110286379/100000000000000 : ℝ), (12413923704847/25000000000000 : ℝ), (8467438975451/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-257601453/2000000000 : ℝ)|^5439 ≤ (8007110286379/100000000000000 : ℝ)^4415
        have hw : |(-257601453/2000000000 : ℝ)|=(257601453/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(566511771/1000000000 : ℝ)|^5439 ≤ (12413923704847/25000000000000 : ℝ)^4415
        have hw : |(566511771/1000000000 : ℝ)|=(566511771/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1244340069/2500000000 : ℝ)|^5439 ≤ (8467438975451/20000000000000 : ℝ)^4415
        have hw : |(1244340069/2500000000 : ℝ)|=(1244340069/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1727_s0_1 (p : ℝ) (hpa : (5431/1024 : ℝ) ≤ p) (hpb : p ≤ (5439/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2696327489/5000000000 : ℝ)*x 0 + (-207306323/1250000000 : ℝ)*x 1 + (39818877/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2696327489/5000000000 : ℝ)^5439 ≤ (46730223210013/100000000000000 : ℝ)^4415 := by
    have hnat : (2696327489 : ℕ)^5439*100000000000000^4415 ≤ 46730223210013^4415*5000000000^5439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696327489 5000000000 46730223210013 100000000000000 5439 4415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (207306323/1250000000 : ℝ)^5439 ≤ (10932588720869/100000000000000 : ℝ)^4415 := by
    have hnat : (207306323 : ℕ)^5439*100000000000000^4415 ≤ 10932588720869^4415*1250000000^5439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      207306323 1250000000 10932588720869 100000000000000 5439 4415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (39818877/80000000 : ℝ)^5439 ≤ (42337188055559/100000000000000 : ℝ)^4415 := by
    have hnat : (39818877 : ℕ)^5439*100000000000000^4415 ≤ 42337188055559^4415*80000000^5439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      39818877 80000000 42337188055559 100000000000000 5439 4415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5439/1024 : ℝ)) 5439 4415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2696327489/5000000000 : ℝ), (-207306323/1250000000 : ℝ), (39818877/80000000 : ℝ)] ![(46730223210013/100000000000000 : ℝ), (10932588720869/100000000000000 : ℝ), (42337188055559/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2696327489/5000000000 : ℝ)|^5439 ≤ (46730223210013/100000000000000 : ℝ)^4415
        have hw : |(2696327489/5000000000 : ℝ)|=(2696327489/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-207306323/1250000000 : ℝ)|^5439 ≤ (10932588720869/100000000000000 : ℝ)^4415
        have hw : |(-207306323/1250000000 : ℝ)|=(207306323/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(39818877/80000000 : ℝ)|^5439 ≤ (42337188055559/100000000000000 : ℝ)^4415
        have hw : |(39818877/80000000 : ℝ)|=(39818877/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1727_s0_2 (p : ℝ) (hpa : (5431/1024 : ℝ) ≤ p) (hpb : p ≤ (5439/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1348163409/2500000000 : ℝ)*x 0 + (311085029/625000000 : ℝ)*x 1 + (-331690253/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1348163409/2500000000 : ℝ)^5439 ≤ (23365104441823/50000000000000 : ℝ)^4415 := by
    have hnat : (1348163409 : ℕ)^5439*50000000000000^4415 ≤ 23365104441823^4415*2500000000^5439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348163409 2500000000 23365104441823 50000000000000 5439 4415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (311085029/625000000 : ℝ)^5439 ≤ (10584299211817/25000000000000 : ℝ)^4415 := by
    have hnat : (311085029 : ℕ)^5439*25000000000000^4415 ≤ 10584299211817^4415*625000000^5439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      311085029 625000000 10584299211817 25000000000000 5439 4415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (331690253/2000000000 : ℝ)^5439 ≤ (10932594251261/100000000000000 : ℝ)^4415 := by
    have hnat : (331690253 : ℕ)^5439*100000000000000^4415 ≤ 10932594251261^4415*2000000000^5439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      331690253 2000000000 10932594251261 100000000000000 5439 4415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5439/1024 : ℝ)) 5439 4415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1348163409/2500000000 : ℝ), (311085029/625000000 : ℝ), (-331690253/2000000000 : ℝ)] ![(23365104441823/50000000000000 : ℝ), (10584299211817/25000000000000 : ℝ), (10932594251261/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1348163409/2500000000 : ℝ)|^5439 ≤ (23365104441823/50000000000000 : ℝ)^4415
        have hw : |(1348163409/2500000000 : ℝ)|=(1348163409/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(311085029/625000000 : ℝ)|^5439 ≤ (10584299211817/25000000000000 : ℝ)^4415
        have hw : |(311085029/625000000 : ℝ)|=(311085029/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-331690253/2000000000 : ℝ)|^5439 ≤ (10932594251261/100000000000000 : ℝ)^4415
        have hw : |(-331690253/2000000000 : ℝ)|=(331690253/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1727_s0_3 (p : ℝ) (hpa : (5431/1024 : ℝ) ≤ p) (hpb : p ≤ (5439/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4025519633/10000000000 : ℝ)*x 0 + (1534897549/5000000000 : ℝ)*x 1 + (5141261299/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4025519633/10000000000 : ℝ)^5439 ≤ (32596104657621/100000000000000 : ℝ)^4415 := by
    have hnat : (4025519633 : ℕ)^5439*100000000000000^4415 ≤ 32596104657621^4415*10000000000^5439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4025519633 10000000000 32596104657621 100000000000000 5439 4415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1534897549/5000000000 : ℝ)^5439 ≤ (2334271104031/10000000000000 : ℝ)^4415 := by
    have hnat : (1534897549 : ℕ)^5439*10000000000000^4415 ≤ 2334271104031^4415*5000000000^5439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1534897549 5000000000 2334271104031 10000000000000 5439 4415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5141261299/10000000000 : ℝ)^5439 ≤ (44061184286359/100000000000000 : ℝ)^4415 := by
    have hnat : (5141261299 : ℕ)^5439*100000000000000^4415 ≤ 44061184286359^4415*10000000000^5439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5141261299 10000000000 44061184286359 100000000000000 5439 4415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5439/1024 : ℝ)) 5439 4415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4025519633/10000000000 : ℝ), (1534897549/5000000000 : ℝ), (5141261299/10000000000 : ℝ)] ![(32596104657621/100000000000000 : ℝ), (2334271104031/10000000000000 : ℝ), (44061184286359/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4025519633/10000000000 : ℝ)|^5439 ≤ (32596104657621/100000000000000 : ℝ)^4415
        have hw : |(4025519633/10000000000 : ℝ)|=(4025519633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1534897549/5000000000 : ℝ)|^5439 ≤ (2334271104031/10000000000000 : ℝ)^4415
        have hw : |(1534897549/5000000000 : ℝ)|=(1534897549/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5141261299/10000000000 : ℝ)|^5439 ≤ (44061184286359/100000000000000 : ℝ)^4415
        have hw : |(5141261299/10000000000 : ℝ)|=(5141261299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1727_s0_4 (p : ℝ) (hpa : (5431/1024 : ℝ) ≤ p) (hpb : p ≤ (5439/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1289434047/10000000000 : ℝ)*x 0 + (998788893/2000000000 : ℝ)*x 1 + (2823999839/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1289434047/10000000000 : ℝ)^5439 ≤ (2004509688323/25000000000000 : ℝ)^4415 := by
    have hnat : (1289434047 : ℕ)^5439*25000000000000^4415 ≤ 2004509688323^4415*10000000000^5439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1289434047 10000000000 2004509688323 25000000000000 5439 4415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (998788893/2000000000 : ℝ)^5439 ≤ (5313880536189/12500000000000 : ℝ)^4415 := by
    have hnat : (998788893 : ℕ)^5439*12500000000000^4415 ≤ 5313880536189^4415*2000000000^5439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      998788893 2000000000 5313880536189 12500000000000 5439 4415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2823999839/5000000000 : ℝ)^5439 ≤ (6183864617343/12500000000000 : ℝ)^4415 := by
    have hnat : (2823999839 : ℕ)^5439*12500000000000^4415 ≤ 6183864617343^4415*5000000000^5439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2823999839 5000000000 6183864617343 12500000000000 5439 4415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5439/1024 : ℝ)) 5439 4415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1289434047/10000000000 : ℝ), (998788893/2000000000 : ℝ), (2823999839/5000000000 : ℝ)] ![(2004509688323/25000000000000 : ℝ), (5313880536189/12500000000000 : ℝ), (6183864617343/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1289434047/10000000000 : ℝ)|^5439 ≤ (2004509688323/25000000000000 : ℝ)^4415
        have hw : |(-1289434047/10000000000 : ℝ)|=(1289434047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(998788893/2000000000 : ℝ)|^5439 ≤ (5313880536189/12500000000000 : ℝ)^4415
        have hw : |(998788893/2000000000 : ℝ)|=(998788893/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2823999839/5000000000 : ℝ)|^5439 ≤ (6183864617343/12500000000000 : ℝ)^4415
        have hw : |(2823999839/5000000000 : ℝ)|=(2823999839/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1727_s0_5 (p : ℝ) (hpa : (5431/1024 : ℝ) ≤ p) (hpb : p ≤ (5439/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1041371279/2000000000 : ℝ)*x 0 + (-987810869/10000000000 : ℝ)*x 1 + (5647999821/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1041371279/2000000000 : ℝ)^5439 ≤ (8950949557433/20000000000000 : ℝ)^4415 := by
    have hnat : (1041371279 : ℕ)^5439*20000000000000^4415 ≤ 8950949557433^4415*2000000000^5439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1041371279 2000000000 8950949557433 20000000000000 5439 4415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (987810869/10000000000 : ℝ)^5439 ≤ (2887166862321/50000000000000 : ℝ)^4415 := by
    have hnat : (987810869 : ℕ)^5439*50000000000000^4415 ≤ 2887166862321^4415*10000000000^5439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      987810869 10000000000 2887166862321 50000000000000 5439 4415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5647999821/10000000000 : ℝ)^5439 ≤ (49470918481793/100000000000000 : ℝ)^4415 := by
    have hnat : (5647999821 : ℕ)^5439*100000000000000^4415 ≤ 49470918481793^4415*10000000000^5439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5647999821 10000000000 49470918481793 100000000000000 5439 4415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5439/1024 : ℝ)) 5439 4415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1041371279/2000000000 : ℝ), (-987810869/10000000000 : ℝ), (5647999821/10000000000 : ℝ)] ![(8950949557433/20000000000000 : ℝ), (2887166862321/50000000000000 : ℝ), (49470918481793/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1041371279/2000000000 : ℝ)|^5439 ≤ (8950949557433/20000000000000 : ℝ)^4415
        have hw : |(1041371279/2000000000 : ℝ)|=(1041371279/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-987810869/10000000000 : ℝ)|^5439 ≤ (2887166862321/50000000000000 : ℝ)^4415
        have hw : |(-987810869/10000000000 : ℝ)|=(987810869/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5647999821/10000000000 : ℝ)|^5439 ≤ (49470918481793/100000000000000 : ℝ)^4415
        have hw : |(5647999821/10000000000 : ℝ)|=(5647999821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1727_s0_6 (p : ℝ) (hpa : (5431/1024 : ℝ) ≤ p) (hpb : p ≤ (5439/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (650857001/1250000000 : ℝ)*x 0 + (5647999743/10000000000 : ℝ)*x 1 + (-493905777/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (650857001/1250000000 : ℝ)^5439 ≤ (44754743689251/100000000000000 : ℝ)^4415 := by
    have hnat : (650857001 : ℕ)^5439*100000000000000^4415 ≤ 44754743689251^4415*1250000000^5439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      650857001 1250000000 44754743689251 100000000000000 5439 4415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5647999743/10000000000 : ℝ)^5439 ≤ (4947091764013/10000000000000 : ℝ)^4415 := by
    have hnat : (5647999743 : ℕ)^5439*10000000000000^4415 ≤ 4947091764013^4415*10000000000^5439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5647999743 10000000000 4947091764013 10000000000000 5439 4415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (493905777/5000000000 : ℝ)^5439 ≤ (1154867731519/20000000000000 : ℝ)^4415 := by
    have hnat : (493905777 : ℕ)^5439*20000000000000^4415 ≤ 1154867731519^4415*5000000000^5439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      493905777 5000000000 1154867731519 20000000000000 5439 4415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5439/1024 : ℝ)) 5439 4415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(650857001/1250000000 : ℝ), (5647999743/10000000000 : ℝ), (-493905777/5000000000 : ℝ)] ![(44754743689251/100000000000000 : ℝ), (4947091764013/10000000000000 : ℝ), (1154867731519/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(650857001/1250000000 : ℝ)|^5439 ≤ (44754743689251/100000000000000 : ℝ)^4415
        have hw : |(650857001/1250000000 : ℝ)|=(650857001/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5647999743/10000000000 : ℝ)|^5439 ≤ (4947091764013/10000000000000 : ℝ)^4415
        have hw : |(5647999743/10000000000 : ℝ)|=(5647999743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-493905777/5000000000 : ℝ)|^5439 ≤ (1154867731519/20000000000000 : ℝ)^4415
        have hw : |(-493905777/5000000000 : ℝ)|=(493905777/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1727_s0_7 (p : ℝ) (hpa : (5431/1024 : ℝ) ≤ p) (hpb : p ≤ (5439/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4029814391/10000000000 : ℝ)*x 0 + (509131301/1000000000 : ℝ)*x 1 + (780337987/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4029814391/10000000000 : ℝ)^5439 ≤ (6527790412387/20000000000000 : ℝ)^4415 := by
    have hnat : (4029814391 : ℕ)^5439*20000000000000^4415 ≤ 6527790412387^4415*10000000000^5439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4029814391 10000000000 6527790412387 20000000000000 5439 4415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (509131301/1000000000 : ℝ)^5439 ≤ (43534434149479/100000000000000 : ℝ)^4415 := by
    have hnat : (509131301 : ℕ)^5439*100000000000000^4415 ≤ 43534434149479^4415*1000000000^5439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      509131301 1000000000 43534434149479 100000000000000 5439 4415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (780337987/2500000000 : ℝ)^5439 ≤ (23826613767523/100000000000000 : ℝ)^4415 := by
    have hnat : (780337987 : ℕ)^5439*100000000000000^4415 ≤ 23826613767523^4415*2500000000^5439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      780337987 2500000000 23826613767523 100000000000000 5439 4415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5439/1024 : ℝ)) 5439 4415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4029814391/10000000000 : ℝ), (509131301/1000000000 : ℝ), (780337987/2500000000 : ℝ)] ![(6527790412387/20000000000000 : ℝ), (43534434149479/100000000000000 : ℝ), (23826613767523/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4029814391/10000000000 : ℝ)|^5439 ≤ (6527790412387/20000000000000 : ℝ)^4415
        have hw : |(4029814391/10000000000 : ℝ)|=(4029814391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(509131301/1000000000 : ℝ)|^5439 ≤ (43534434149479/100000000000000 : ℝ)^4415
        have hw : |(509131301/1000000000 : ℝ)|=(509131301/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(780337987/2500000000 : ℝ)|^5439 ≤ (23826613767523/100000000000000 : ℝ)^4415
        have hw : |(780337987/2500000000 : ℝ)|=(780337987/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1727_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5431/1024 : ℝ) ≤ p) (hpb : p ≤ (5439/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (8023833/4000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (6521/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (5333/25000 : ℝ)*pair X 0 0 := by
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
  have base16 : ((-1 : ℝ)*X 1 1+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 1).1]
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
  have hpowlo : (0 : ℝ) ^ (5431/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^5431 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^5431*1^1024 ≤ 0^1024*1^5431 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 5431 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 5431 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (5431/1024 : ℝ) ≤ (775249015757825849/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^5431 ≤ (775249015757825849/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^5431*100000000000000000000^1024 ≤ 775249015757825849^1024*5^5431 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 775249015757825849 100000000000000000000 5431 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (775249015757825849/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5431 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (5431/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^5431 := by
      have hnat : (1 : ℕ)^1024*1^5431 ≤ 1^5431*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 5431 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 5431 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100775249015757825849/100000000000000000000 : ℝ) ≤ (31295535446627/31250000000000 : ℝ) ^ (5431/1024 : ℝ) := by
    have hpowers : (100775249015757825849/100000000000000000000 : ℝ)^1024 ≤ (31295535446627/31250000000000 : ℝ)^5431 := by
      have hnat : (100775249015757825849 : ℕ)^1024*31250000000000^5431 ≤ 31295535446627^5431*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100775249015757825849 100000000000000000000 31295535446627 31250000000000 1024 5431 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (31295535446627/31250000000000 : ℝ)) (X := (100775249015757825849/100000000000000000000 : ℝ)) (by norm_num) 5431 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50775249015757825849/50000000000000000000 : ℝ) ≤ (15670535446627/15625000000000 : ℝ) ^ (5431/1024 : ℝ) := by
    have hpowers : (50775249015757825849/50000000000000000000 : ℝ)^1024 ≤ (15670535446627/15625000000000 : ℝ)^5431 := by
      have hnat : (50775249015757825849 : ℕ)^1024*15625000000000^5431 ≤ 15670535446627^5431*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50775249015757825849 50000000000000000000 15670535446627 15625000000000 1024 5431 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (15670535446627/15625000000000 : ℝ)) (X := (50775249015757825849/50000000000000000000 : ℝ)) (by norm_num) 5431 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(45535446627/12500000000000 : ℝ)*(0 : ℝ))^(5431/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(45535446627/12500000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(775249015757825849/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(45535446627/12500000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(5431/1024 : ℝ) := by
    rw [show (1 : ℝ)+(45535446627/12500000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(31295535446627/31250000000000 : ℝ) by norm_num, show 1+(775249015757825849/100000000000000000000 : ℝ)+(0 : ℝ)=(100775249015757825849/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(775249015757825849/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(45535446627/12500000000000 : ℝ)*(2/5 : ℝ))^(5431/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(45535446627/12500000000000 : ℝ)*(2/5 : ℝ)=(15670535446627/15625000000000 : ℝ) by norm_num, show 1+2*(775249015757825849/100000000000000000000 : ℝ)=(50775249015757825849/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(45535446627/12500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5431/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (45535446627/12500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(45535446627/12500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5431/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (45535446627/12500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(45535446627/12500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5431/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (45535446627/12500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-257601453/2000000000 : ℝ)*X 0 0+(566511771/1000000000 : ℝ)*X 0 1+(1244340069/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1727_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2696327489/5000000000 : ℝ)*X 1 0+(-207306323/1250000000 : ℝ)*X 1 1+(39818877/80000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1727_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1348163409/2500000000 : ℝ)*X 2 0+(311085029/625000000 : ℝ)*X 2 1+(-331690253/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1727_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4025519633/10000000000 : ℝ)*X 0 0+(1534897549/5000000000 : ℝ)*X 0 1+(5141261299/10000000000 : ℝ)*X 0 2+(4025519633/10000000000 : ℝ)*X 1 0+(1534897549/5000000000 : ℝ)*X 1 1+(5141261299/10000000000 : ℝ)*X 1 2+(4025519633/10000000000 : ℝ)*X 2 0+(1534897549/5000000000 : ℝ)*X 2 1+(5141261299/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1727_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1289434047/10000000000 : ℝ)*X 0 0+(998788893/2000000000 : ℝ)*X 0 1+(2823999839/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1727_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1041371279/2000000000 : ℝ)*X 1 0+(-987810869/10000000000 : ℝ)*X 1 1+(5647999821/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1727_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((650857001/1250000000 : ℝ)*X 2 0+(5647999743/10000000000 : ℝ)*X 2 1+(-493905777/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1727_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4029814391/10000000000 : ℝ)*X 0 0+(509131301/1000000000 : ℝ)*X 0 1+(780337987/2500000000 : ℝ)*X 0 2+(4029814391/10000000000 : ℝ)*X 1 0+(509131301/1000000000 : ℝ)*X 1 1+(780337987/2500000000 : ℝ)*X 1 2+(4029814391/10000000000 : ℝ)*X 2 0+(509131301/1000000000 : ℝ)*X 2 1+(780337987/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1727_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1327277133614081135091/625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (17825807/10000000000000 : ℝ)*(base1) + (1720621/25000000000000 : ℝ)*(base16) + (325811441/50000000000000 : ℝ)*(base19) + (129616013/50000000000000 : ℝ)*(base23) + (140480029/100000000000000 : ℝ)*(upper3) + (968376522895637/100000000000000 : ℝ)*(major0) + (968376522895637/100000000000000 : ℝ)*(major1) + (968376522895637/100000000000000 : ℝ)*(major2) + (727001532335539/50000000000000 : ℝ)*(sp0) + (727001113953821/50000000000000 : ℝ)*(sp1) + (90875096291647/6250000000000 : ℝ)*(sp2) + (120687435968837/25000000000000 : ℝ)*(sp3) + (108651463/10000000000000 : ℝ)*(sp6) + (16645673/10000000000000 : ℝ)*(sp7) + (120687522147537/25000000000000 : ℝ)*(f.failure) + (90875180400813/6250000000000 : ℝ)*(f.sum) + (635474736101/625000000000000000000000000 : ℝ)*base66 + (4836761313601/1250000000000000000000000000 : ℝ)*base68 + (8426726108601/1250000000000000000000000000 : ℝ)*base70 + (4711708571101/1250000000000000000000000000 : ℝ)*base72 + (1689893118899/625000000000000000000000000 : ℝ)*base73 + (477702988899/1250000000000000000000000000 : ℝ)*base75 + (1981097366101/1250000000000000000000000000 : ℝ)*base78 + (5290581361101/1250000000000000000000000000 : ℝ)*base80 + (3299393328601/625000000000000000000000000 : ℝ)*base82 + (1249321/100000000000000000000 : ℝ)*base89 + (1249321/100000000000000000000 : ℝ)*base91 + (1249321/100000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (202544255166839496789/78125000000000000000000000 : ℝ) := by norm_num
    linear_combination (687568253/100000000000000 : ℝ)*(base19) + (29582159/5000000000000 : ℝ)*(base23) + (30408301/100000000000000 : ℝ)*(upper2) + (126845683/100000000000000 : ℝ)*(upper3) + (16334953/20000000000000 : ℝ)*(upper5) + (254568280284329/25000000000000 : ℝ)*(major0) + (254568280284329/25000000000000 : ℝ)*(major1) + (254568280284329/25000000000000 : ℝ)*(major2) + (57929011/2000000000000 : ℝ)*(sp1) + (109762517/6250000000000 : ℝ)*(sp2) + (1528921871483269/100000000000000 : ℝ)*(sp4) + (764459143732233/50000000000000 : ℝ)*(sp5) + (1528919523639817/100000000000000 : ℝ)*(sp6) + (507624284372477/100000000000000 : ℝ)*(sp7) + (507624284372477/100000000000000 : ℝ)*(f.failure) + (1528921871483269/100000000000000 : ℝ)*(f.sum) + (367773873283/156250000000000000000000000 : ℝ)*base65 + (4479951857191/625000000000000000000000000 : ℝ)*base67 + (338955898671/156250000000000000000000000 : ℝ)*base70 + (769993968441/625000000000000000000000000 : ℝ)*base71 + (224669693283/156250000000000000000000000 : ℝ)*base73 + (1448176654533/312500000000000000000000000 : ℝ)*base75 + (6142642994691/625000000000000000000000000 : ℝ)*base77 + (106978635941/625000000000000000000000000 : ℝ)*base79 + (1827979951559/312500000000000000000000000 : ℝ)*base82 + (1244341/400000000000000000000 : ℝ)*base89 + (1244341/400000000000000000000 : ℝ)*base91 + (1244341/400000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1727_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5431/1024 : ℝ) ≤ p) (hpb : p ≤ (5439/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (8023833/4000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (6521/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (5333/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1727_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1727_s1_0 (p : ℝ) (hpa : (5431/1024 : ℝ) ≤ p) (hpb : p ≤ (5439/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1350450939/10000000000 : ℝ)*x 0 + (5469748549/10000000000 : ℝ)*x 1 + (5131430953/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1350450939/10000000000 : ℝ)^5439 ≤ (424399677173/5000000000000 : ℝ)^4415 := by
    have hnat : (1350450939 : ℕ)^5439*5000000000000^4415 ≤ 424399677173^4415*10000000000^5439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1350450939 10000000000 424399677173 5000000000000 5439 4415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5469748549/10000000000 : ℝ)^5439 ≤ (23777293146193/50000000000000 : ℝ)^4415 := by
    have hnat : (5469748549 : ℕ)^5439*50000000000000^4415 ≤ 23777293146193^4415*10000000000^5439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5469748549 10000000000 23777293146193 50000000000000 5439 4415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5131430953/10000000000 : ℝ)^5439 ≤ (4395742014733/10000000000000 : ℝ)^4415 := by
    have hnat : (5131430953 : ℕ)^5439*10000000000000^4415 ≤ 4395742014733^4415*10000000000^5439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5131430953 10000000000 4395742014733 10000000000000 5439 4415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5439/1024 : ℝ)) 5439 4415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1350450939/10000000000 : ℝ), (5469748549/10000000000 : ℝ), (5131430953/10000000000 : ℝ)] ![(424399677173/5000000000000 : ℝ), (23777293146193/50000000000000 : ℝ), (4395742014733/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1350450939/10000000000 : ℝ)|^5439 ≤ (424399677173/5000000000000 : ℝ)^4415
        have hw : |(-1350450939/10000000000 : ℝ)|=(1350450939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5469748549/10000000000 : ℝ)|^5439 ≤ (23777293146193/50000000000000 : ℝ)^4415
        have hw : |(5469748549/10000000000 : ℝ)|=(5469748549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5131430953/10000000000 : ℝ)|^5439 ≤ (4395742014733/10000000000000 : ℝ)^4415
        have hw : |(5131430953/10000000000 : ℝ)|=(5131430953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1727_s1_1 (p : ℝ) (hpa : (5431/1024 : ℝ) ≤ p) (hpb : p ≤ (5439/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5340629801/10000000000 : ℝ)*x 0 + (-1525999971/10000000000 : ℝ)*x 1 + (2565715011/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5340629801/10000000000 : ℝ)^5439 ≤ (46175457291147/100000000000000 : ℝ)^4415 := by
    have hnat : (5340629801 : ℕ)^5439*100000000000000^4415 ≤ 46175457291147^4415*10000000000^5439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5340629801 10000000000 46175457291147 100000000000000 5439 4415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1525999971/10000000000 : ℝ)^5439 ≤ (2466783092179/25000000000000 : ℝ)^4415 := by
    have hnat : (1525999971 : ℕ)^5439*25000000000000^4415 ≤ 2466783092179^4415*10000000000^5439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1525999971 10000000000 2466783092179 25000000000000 5439 4415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2565715011/5000000000 : ℝ)^5439 ≤ (43957410322349/100000000000000 : ℝ)^4415 := by
    have hnat : (2565715011 : ℕ)^5439*100000000000000^4415 ≤ 43957410322349^4415*5000000000^5439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2565715011 5000000000 43957410322349 100000000000000 5439 4415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5439/1024 : ℝ)) 5439 4415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5340629801/10000000000 : ℝ), (-1525999971/10000000000 : ℝ), (2565715011/5000000000 : ℝ)] ![(46175457291147/100000000000000 : ℝ), (2466783092179/25000000000000 : ℝ), (43957410322349/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5340629801/10000000000 : ℝ)|^5439 ≤ (46175457291147/100000000000000 : ℝ)^4415
        have hw : |(5340629801/10000000000 : ℝ)|=(5340629801/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1525999971/10000000000 : ℝ)|^5439 ≤ (2466783092179/25000000000000 : ℝ)^4415
        have hw : |(-1525999971/10000000000 : ℝ)|=(1525999971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2565715011/5000000000 : ℝ)|^5439 ≤ (43957410322349/100000000000000 : ℝ)^4415
        have hw : |(2565715011/5000000000 : ℝ)|=(2565715011/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1727_s1_2 (p : ℝ) (hpa : (5431/1024 : ℝ) ≤ p) (hpb : p ≤ (5439/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2670314241/5000000000 : ℝ)*x 0 + (5131430899/10000000000 : ℝ)*x 1 + (-1526000573/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2670314241/5000000000 : ℝ)^5439 ≤ (23087721620969/50000000000000 : ℝ)^4415 := by
    have hnat : (2670314241 : ℕ)^5439*50000000000000^4415 ≤ 23087721620969^4415*5000000000^5439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2670314241 5000000000 23087721620969 50000000000000 5439 4415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5131430899/10000000000 : ℝ)^5439 ≤ (2197870978873/5000000000000 : ℝ)^4415 := by
    have hnat : (5131430899 : ℕ)^5439*5000000000000^4415 ≤ 2197870978873^4415*10000000000^5439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5131430899 10000000000 2197870978873 5000000000000 5439 4415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1526000573/10000000000 : ℝ)^5439 ≤ (9867137164077/100000000000000 : ℝ)^4415 := by
    have hnat : (1526000573 : ℕ)^5439*100000000000000^4415 ≤ 9867137164077^4415*10000000000^5439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1526000573 10000000000 9867137164077 100000000000000 5439 4415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5439/1024 : ℝ)) 5439 4415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2670314241/5000000000 : ℝ), (5131430899/10000000000 : ℝ), (-1526000573/10000000000 : ℝ)] ![(23087721620969/50000000000000 : ℝ), (2197870978873/5000000000000 : ℝ), (9867137164077/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2670314241/5000000000 : ℝ)|^5439 ≤ (23087721620969/50000000000000 : ℝ)^4415
        have hw : |(2670314241/5000000000 : ℝ)|=(2670314241/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5131430899/10000000000 : ℝ)|^5439 ≤ (2197870978873/5000000000000 : ℝ)^4415
        have hw : |(5131430899/10000000000 : ℝ)|=(5131430899/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1526000573/10000000000 : ℝ)|^5439 ≤ (9867137164077/100000000000000 : ℝ)^4415
        have hw : |(-1526000573/10000000000 : ℝ)|=(1526000573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1727_s1_3 (p : ℝ) (hpa : (5431/1024 : ℝ) ≤ p) (hpb : p ≤ (5439/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2040765799/5000000000 : ℝ)*x 0 + (3591287869/10000000000 : ℝ)*x 1 + (1152566747/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2040765799/5000000000 : ℝ)^5439 ≤ (33155747112943/100000000000000 : ℝ)^4415 := by
    have hnat : (2040765799 : ℕ)^5439*100000000000000^4415 ≤ 33155747112943^4415*5000000000^5439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2040765799 5000000000 33155747112943 100000000000000 5439 4415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3591287869/10000000000 : ℝ)^5439 ≤ (28320210385513/100000000000000 : ℝ)^4415 := by
    have hnat : (3591287869 : ℕ)^5439*100000000000000^4415 ≤ 28320210385513^4415*10000000000^5439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3591287869 10000000000 28320210385513 100000000000000 5439 4415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1152566747/2500000000 : ℝ)^5439 ≤ (19262021244361/50000000000000 : ℝ)^4415 := by
    have hnat : (1152566747 : ℕ)^5439*50000000000000^4415 ≤ 19262021244361^4415*2500000000^5439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1152566747 2500000000 19262021244361 50000000000000 5439 4415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5439/1024 : ℝ)) 5439 4415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2040765799/5000000000 : ℝ), (3591287869/10000000000 : ℝ), (1152566747/2500000000 : ℝ)] ![(33155747112943/100000000000000 : ℝ), (28320210385513/100000000000000 : ℝ), (19262021244361/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2040765799/5000000000 : ℝ)|^5439 ≤ (33155747112943/100000000000000 : ℝ)^4415
        have hw : |(2040765799/5000000000 : ℝ)|=(2040765799/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3591287869/10000000000 : ℝ)|^5439 ≤ (28320210385513/100000000000000 : ℝ)^4415
        have hw : |(3591287869/10000000000 : ℝ)|=(3591287869/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1152566747/2500000000 : ℝ)|^5439 ≤ (19262021244361/50000000000000 : ℝ)^4415
        have hw : |(1152566747/2500000000 : ℝ)|=(1152566747/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1727_s1_4 (p : ℝ) (hpa : (5431/1024 : ℝ) ≤ p) (hpb : p ≤ (5439/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-337655201/2500000000 : ℝ)*x 0 + (5135457673/10000000000 : ℝ)*x 1 + (5465657501/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (337655201/2500000000 : ℝ)^5439 ≤ (1697861768691/20000000000000 : ℝ)^4415 := by
    have hnat : (337655201 : ℕ)^5439*20000000000000^4415 ≤ 1697861768691^4415*2500000000^5439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337655201 2500000000 1697861768691 20000000000000 5439 4415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5135457673/10000000000 : ℝ)^5439 ≤ (8799983717709/20000000000000 : ℝ)^4415 := by
    have hnat : (5135457673 : ℕ)^5439*20000000000000^4415 ≤ 8799983717709^4415*10000000000^5439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5135457673 10000000000 8799983717709 20000000000000 5439 4415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5465657501/10000000000 : ℝ)^5439 ≤ (1900430902229/4000000000000 : ℝ)^4415 := by
    have hnat : (5465657501 : ℕ)^5439*4000000000000^4415 ≤ 1900430902229^4415*10000000000^5439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5465657501 10000000000 1900430902229 4000000000000 5439 4415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5439/1024 : ℝ)) 5439 4415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-337655201/2500000000 : ℝ), (5135457673/10000000000 : ℝ), (5465657501/10000000000 : ℝ)] ![(1697861768691/20000000000000 : ℝ), (8799983717709/20000000000000 : ℝ), (1900430902229/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-337655201/2500000000 : ℝ)|^5439 ≤ (1697861768691/20000000000000 : ℝ)^4415
        have hw : |(-337655201/2500000000 : ℝ)|=(337655201/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5135457673/10000000000 : ℝ)|^5439 ≤ (8799983717709/20000000000000 : ℝ)^4415
        have hw : |(5135457673/10000000000 : ℝ)|=(5135457673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5465657501/10000000000 : ℝ)|^5439 ≤ (1900430902229/4000000000000 : ℝ)^4415
        have hw : |(5465657501/10000000000 : ℝ)|=(5465657501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1727_s1_5 (p : ℝ) (hpa : (5431/1024 : ℝ) ≤ p) (hpb : p ≤ (5439/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5250055301/10000000000 : ℝ)*x 0 + (-1191773627/10000000000 : ℝ)*x 1 + (1366414303/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5250055301/10000000000 : ℝ)^5439 ≤ (9042523386701/20000000000000 : ℝ)^4415 := by
    have hnat : (5250055301 : ℕ)^5439*20000000000000^4415 ≤ 9042523386701^4415*10000000000^5439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5250055301 10000000000 9042523386701 20000000000000 5439 4415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1191773627/10000000000 : ℝ)^5439 ≤ (7276613592141/100000000000000 : ℝ)^4415 := by
    have hnat : (1191773627 : ℕ)^5439*100000000000000^4415 ≤ 7276613592141^4415*10000000000^5439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1191773627 10000000000 7276613592141 100000000000000 5439 4415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1366414303/2500000000 : ℝ)^5439 ≤ (47510769460901/100000000000000 : ℝ)^4415 := by
    have hnat : (1366414303 : ℕ)^5439*100000000000000^4415 ≤ 47510769460901^4415*2500000000^5439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1366414303 2500000000 47510769460901 100000000000000 5439 4415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5439/1024 : ℝ)) 5439 4415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5250055301/10000000000 : ℝ), (-1191773627/10000000000 : ℝ), (1366414303/2500000000 : ℝ)] ![(9042523386701/20000000000000 : ℝ), (7276613592141/100000000000000 : ℝ), (47510769460901/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5250055301/10000000000 : ℝ)|^5439 ≤ (9042523386701/20000000000000 : ℝ)^4415
        have hw : |(5250055301/10000000000 : ℝ)|=(5250055301/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1191773627/10000000000 : ℝ)|^5439 ≤ (7276613592141/100000000000000 : ℝ)^4415
        have hw : |(-1191773627/10000000000 : ℝ)|=(1191773627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1366414303/2500000000 : ℝ)|^5439 ≤ (47510769460901/100000000000000 : ℝ)^4415
        have hw : |(1366414303/2500000000 : ℝ)|=(1366414303/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1727_s1_6 (p : ℝ) (hpa : (5431/1024 : ℝ) ≤ p) (hpb : p ≤ (5439/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2625027601/5000000000 : ℝ)*x 0 + (683207139/1250000000 : ℝ)*x 1 + (-1191773909/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2625027601/5000000000 : ℝ)^5439 ≤ (45212615883191/100000000000000 : ℝ)^4415 := by
    have hnat : (2625027601 : ℕ)^5439*100000000000000^4415 ≤ 45212615883191^4415*5000000000^5439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2625027601 5000000000 45212615883191 100000000000000 5439 4415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (683207139/1250000000 : ℝ)^5439 ≤ (11877692097507/25000000000000 : ℝ)^4415 := by
    have hnat : (683207139 : ℕ)^5439*25000000000000^4415 ≤ 11877692097507^4415*1250000000^5439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      683207139 1250000000 11877692097507 25000000000000 5439 4415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1191773909/10000000000 : ℝ)^5439 ≤ (7276615713299/100000000000000 : ℝ)^4415 := by
    have hnat : (1191773909 : ℕ)^5439*100000000000000^4415 ≤ 7276615713299^4415*10000000000^5439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1191773909 10000000000 7276615713299 100000000000000 5439 4415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5439/1024 : ℝ)) 5439 4415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2625027601/5000000000 : ℝ), (683207139/1250000000 : ℝ), (-1191773909/10000000000 : ℝ)] ![(45212615883191/100000000000000 : ℝ), (11877692097507/25000000000000 : ℝ), (7276615713299/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2625027601/5000000000 : ℝ)|^5439 ≤ (45212615883191/100000000000000 : ℝ)^4415
        have hw : |(2625027601/5000000000 : ℝ)|=(2625027601/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(683207139/1250000000 : ℝ)|^5439 ≤ (11877692097507/25000000000000 : ℝ)^4415
        have hw : |(683207139/1250000000 : ℝ)|=(683207139/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1191773909/10000000000 : ℝ)|^5439 ≤ (7276615713299/100000000000000 : ℝ)^4415
        have hw : |(-1191773909/10000000000 : ℝ)|=(1191773909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1727_s1_7 (p : ℝ) (hpa : (5431/1024 : ℝ) ≤ p) (hpb : p ≤ (5439/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4082039643/10000000000 : ℝ)*x 0 + (574767417/1250000000 : ℝ)*x 1 + (3603606673/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4082039643/10000000000 : ℝ)^5439 ≤ (8290207857007/25000000000000 : ℝ)^4415 := by
    have hnat : (4082039643 : ℕ)^5439*25000000000000^4415 ≤ 8290207857007^4415*10000000000^5439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4082039643 10000000000 8290207857007 25000000000000 5439 4415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (574767417/1250000000 : ℝ)^5439 ≤ (38399235686217/100000000000000 : ℝ)^4415 := by
    have hnat : (574767417 : ℕ)^5439*100000000000000^4415 ≤ 38399235686217^4415*1250000000^5439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      574767417 1250000000 38399235686217 100000000000000 5439 4415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3603606673/10000000000 : ℝ)^5439 ≤ (14219966435829/50000000000000 : ℝ)^4415 := by
    have hnat : (3603606673 : ℕ)^5439*50000000000000^4415 ≤ 14219966435829^4415*10000000000^5439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3603606673 10000000000 14219966435829 50000000000000 5439 4415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5439/1024 : ℝ)) 5439 4415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4082039643/10000000000 : ℝ), (574767417/1250000000 : ℝ), (3603606673/10000000000 : ℝ)] ![(8290207857007/25000000000000 : ℝ), (38399235686217/100000000000000 : ℝ), (14219966435829/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4082039643/10000000000 : ℝ)|^5439 ≤ (8290207857007/25000000000000 : ℝ)^4415
        have hw : |(4082039643/10000000000 : ℝ)|=(4082039643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(574767417/1250000000 : ℝ)|^5439 ≤ (38399235686217/100000000000000 : ℝ)^4415
        have hw : |(574767417/1250000000 : ℝ)|=(574767417/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3603606673/10000000000 : ℝ)|^5439 ≤ (14219966435829/50000000000000 : ℝ)^4415
        have hw : |(3603606673/10000000000 : ℝ)|=(3603606673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1727_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5431/1024 : ℝ) ≤ p) (hpb : p ≤ (5439/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (8023833/4000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (5333/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (6521/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (4973/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (17189/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (5333/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (6521/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (5333/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (6521/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (5333/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (6521/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (5333/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (6521/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (5333/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (6521/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (5333/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (6521/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (6521/100000 : ℝ) ^ (5431/1024 : ℝ) ≤ (51459463632719/100000000000000000000 : ℝ) := by
    have hpowers : (6521/100000 : ℝ)^5431 ≤ (51459463632719/100000000000000000000 : ℝ)^1024 := by
      have hnat : (6521 : ℕ)^5431*100000000000000000000^1024 ≤ 51459463632719^1024*100000^5431 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6521 100000 51459463632719 100000000000000000000 5431 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6521/100000 : ℝ)) (X := (51459463632719/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5431 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (5333/25000 : ℝ) ^ (5431/1024 : ℝ) ≤ (27629779922001873/100000000000000000000 : ℝ) := by
    have hpowers : (5333/25000 : ℝ)^5431 ≤ (27629779922001873/100000000000000000000 : ℝ)^1024 := by
      have hnat : (5333 : ℕ)^5431*100000000000000000000^1024 ≤ 27629779922001873^1024*25000^5431 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5333 25000 27629779922001873 100000000000000000000 5431 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5333/25000 : ℝ)) (X := (27629779922001873/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5431 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000051459463632719/50000000000000000000 : ℝ) ≤ (2500000485126761/2500000000000000 : ℝ) ^ (5431/1024 : ℝ) := by
    have hpowers : (50000051459463632719/50000000000000000000 : ℝ)^1024 ≤ (2500000485126761/2500000000000000 : ℝ)^5431 := by
      have hnat : (50000051459463632719 : ℕ)^1024*2500000000000000^5431 ≤ 2500000485126761^5431*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000051459463632719 50000000000000000000 2500000485126761 2500000000000000 1024 5431 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500000485126761/2500000000000000 : ℝ)) (X := (50000051459463632719/50000000000000000000 : ℝ)) (by norm_num) 5431 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (3125865038730801081/3125000000000000000 : ℝ) ≤ (5000260931745233/5000000000000000 : ℝ) ^ (5431/1024 : ℝ) := by
    have hpowers : (3125865038730801081/3125000000000000000 : ℝ)^1024 ≤ (5000260931745233/5000000000000000 : ℝ)^5431 := by
      have hnat : (3125865038730801081 : ℕ)^1024*5000000000000000^5431 ≤ 5000260931745233^5431*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3125865038730801081 3125000000000000000 5000260931745233 5000000000000000 1024 5431 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000260931745233/5000000000000000 : ℝ)) (X := (3125865038730801081/3125000000000000000 : ℝ)) (by norm_num) 5431 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50027629779922001873/50000000000000000000 : ℝ) ≤ (312532555827309/312500000000000 : ℝ) ^ (5431/1024 : ℝ) := by
    have hpowers : (50027629779922001873/50000000000000000000 : ℝ)^1024 ≤ (312532555827309/312500000000000 : ℝ)^5431 := by
      have hnat : (50027629779922001873 : ℕ)^1024*312500000000000^5431 ≤ 312532555827309^5431*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50027629779922001873 50000000000000000000 312532555827309 312500000000000 1024 5431 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312532555827309/312500000000000 : ℝ)) (X := (50027629779922001873/50000000000000000000 : ℝ)) (by norm_num) 5431 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(51459463632719/100000000000000000000 : ℝ) ≤ ((1851290598816250487/1851375000000000000 : ℝ)+2*(259961491711/740550000000000 : ℝ)*(6521/100000 : ℝ))^(5431/1024 : ℝ) := by
    rw [show (1851290598816250487/1851375000000000000 : ℝ)+2*(259961491711/740550000000000 : ℝ)*(6521/100000 : ℝ)=(2500000485126761/2500000000000000 : ℝ) by norm_num, show 1+2*(51459463632719/100000000000000000000 : ℝ)=(50000051459463632719/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(27629779922001873/100000000000000000000 : ℝ)+(51459463632719/100000000000000000000 : ℝ) ≤ ((1851290598816250487/1851375000000000000 : ℝ)+(259961491711/740550000000000 : ℝ)*((5333/25000 : ℝ)+(6521/100000 : ℝ)))^(5431/1024 : ℝ) := by
    rw [show (1851290598816250487/1851375000000000000 : ℝ)+(259961491711/740550000000000 : ℝ)*((5333/25000 : ℝ)+(6521/100000 : ℝ))=(5000260931745233/5000000000000000 : ℝ) by norm_num, show 1+(27629779922001873/100000000000000000000 : ℝ)+(51459463632719/100000000000000000000 : ℝ)=(3125865038730801081/3125000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(27629779922001873/100000000000000000000 : ℝ) ≤ ((1851290598816250487/1851375000000000000 : ℝ)+2*(259961491711/740550000000000 : ℝ)*(5333/25000 : ℝ))^(5431/1024 : ℝ) := by
    rw [show (1851290598816250487/1851375000000000000 : ℝ)+2*(259961491711/740550000000000 : ℝ)*(5333/25000 : ℝ)=(312532555827309/312500000000000 : ℝ) by norm_num, show 1+2*(27629779922001873/100000000000000000000 : ℝ)=(50027629779922001873/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1851290598816250487/1851375000000000000 : ℝ)*(X 1 0+X 2 0)+(259961491711/740550000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5431/1024 : ℝ)) (lo := (6521/100000 : ℝ)) (hi := (5333/25000 : ℝ)) (c := (1851290598816250487/1851375000000000000 : ℝ)) (alpha := (259961491711/740550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1851290598816250487/1851375000000000000 : ℝ)*(X 0 1+X 2 1)+(259961491711/740550000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5431/1024 : ℝ)) (lo := (6521/100000 : ℝ)) (hi := (5333/25000 : ℝ)) (c := (1851290598816250487/1851375000000000000 : ℝ)) (alpha := (259961491711/740550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1851290598816250487/1851375000000000000 : ℝ)*(X 0 2+X 1 2)+(259961491711/740550000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5431/1024 : ℝ)) (lo := (6521/100000 : ℝ)) (hi := (5333/25000 : ℝ)) (c := (1851290598816250487/1851375000000000000 : ℝ)) (alpha := (259961491711/740550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1350450939/10000000000 : ℝ)*X 0 0+(5469748549/10000000000 : ℝ)*X 0 1+(5131430953/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1727_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5340629801/10000000000 : ℝ)*X 1 0+(-1525999971/10000000000 : ℝ)*X 1 1+(2565715011/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1727_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2670314241/5000000000 : ℝ)*X 2 0+(5131430899/10000000000 : ℝ)*X 2 1+(-1526000573/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1727_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2040765799/5000000000 : ℝ)*X 0 0+(3591287869/10000000000 : ℝ)*X 0 1+(1152566747/2500000000 : ℝ)*X 0 2+(2040765799/5000000000 : ℝ)*X 1 0+(3591287869/10000000000 : ℝ)*X 1 1+(1152566747/2500000000 : ℝ)*X 1 2+(2040765799/5000000000 : ℝ)*X 2 0+(3591287869/10000000000 : ℝ)*X 2 1+(1152566747/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1727_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-337655201/2500000000 : ℝ)*X 0 0+(5135457673/10000000000 : ℝ)*X 0 1+(5465657501/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1727_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5250055301/10000000000 : ℝ)*X 1 0+(-1191773627/10000000000 : ℝ)*X 1 1+(1366414303/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1727_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2625027601/5000000000 : ℝ)*X 2 0+(683207139/1250000000 : ℝ)*X 2 1+(-1191773909/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1727_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4082039643/10000000000 : ℝ)*X 0 0+(574767417/1250000000 : ℝ)*X 0 1+(3603606673/10000000000 : ℝ)*X 0 2+(4082039643/10000000000 : ℝ)*X 1 0+(574767417/1250000000 : ℝ)*X 1 1+(3603606673/10000000000 : ℝ)*X 1 2+(4082039643/10000000000 : ℝ)*X 2 0+(574767417/1250000000 : ℝ)*X 2 1+(3603606673/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1727_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (24004544481215426448546173/7714062500000000000000000000000 : ℝ) := by norm_num
    linear_combination (198530753/100000000000000 : ℝ)*(base19) + (2412301/25000000000000 : ℝ)*(lower2) + (137802647/50000000000000 : ℝ)*(lower4) + (208628761/100000000000000 : ℝ)*(lower5) + (492149330831357/25000000000000 : ℝ)*(major0) + (492149330831357/25000000000000 : ℝ)*(major1) + (492149330831357/25000000000000 : ℝ)*(major2) + (1477907738907687/50000000000000 : ℝ)*(sp0) + (2955809937694927/100000000000000 : ℝ)*(sp1) + (1477906055569313/50000000000000 : ℝ)*(sp2) + (981375022797921/100000000000000 : ℝ)*(sp3) + (808462243/20000000000000 : ℝ)*(sp4) + (9383900909/100000000000000 : ℝ)*(sp5) + (7408987963/100000000000000 : ℝ)*(sp6) + (981375022797921/100000000000000 : ℝ)*(f.failure) + (2955819520126589/100000000000000 : ℝ)*(f.sum) + (14501630633909/4628437500000000000000000000 : ℝ)*base66 + (60470747234948203/15428125000000000000000000000000 : ℝ)*base67 + (11088393928303457/3857031250000000000000000000000 : ℝ)*base69 + (71873974900610703/15428125000000000000000000000000 : ℝ)*base71 + (229514915622721/74055000000000000000000000000 : ℝ)*base73 + (55923759743823203/15428125000000000000000000000000 : ℝ)*base75 + (65199904996504453/15428125000000000000000000000000 : ℝ)*base77 + (23523733413360039/7714062500000000000000000000000 : ℝ)*base79 + (10060088590949/74055000000000000000000000000 : ℝ)*base82 + (1148807/400000000000000000000 : ℝ)*base90 + (1148807/400000000000000000000 : ℝ)*base92 + (1148807/400000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (38505333315685966194389211/3857031250000000000000000000000 : ℝ) := by norm_num
    linear_combination (30793011/2000000000000 : ℝ)*(base19) + (1484833597/100000000000000 : ℝ)*(base23) + (36455167/100000000000000 : ℝ)*(upper2) + (14178477/10000000000000 : ℝ)*(upper3) + (275647999/100000000000000 : ℝ)*(upper5) + (504245965098381/25000000000000 : ℝ)*(major0) + (504245965098381/25000000000000 : ℝ)*(major1) + (504245965098381/25000000000000 : ℝ)*(major2) + (7013534069/50000000000000 : ℝ)*(sp1) + (40540409/400000000000 : ℝ)*(sp2) + (94639717417889/3125000000000 : ℝ)*(sp4) + (1514227695326879/50000000000000 : ℝ)*(sp5) + (15142296687183/500000000000 : ℝ)*(sp6) + (1005496430642823/100000000000000 : ℝ)*(sp7) + (1005496430642823/100000000000000 : ℝ)*(f.failure) + (94639717417889/3125000000000 : ℝ)*(f.sum) + (73349230020431/24685000000000000000000000000 : ℝ)*base65 + (36323819321778651/15428125000000000000000000000000 : ℝ)*base68 + (81749785384975263/7714062500000000000000000000000 : ℝ)*base70 + (6646801126742319/3857031250000000000000000000000 : ℝ)*base72 + (11290646498067/3085625000000000000000000000 : ℝ)*base73 + (56189151591418487/7714062500000000000000000000000 : ℝ)*base75 + (284873132616921/60266113281250000000000000000 : ℝ)*base78 + (12843633372277599/15428125000000000000000000000000 : ℝ)*base79 + (1938604918511/24685000000000000000000000000 : ℝ)*base81 + (1/50000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (1599441/400000000000000000000 : ℝ)*base90 + (1599441/400000000000000000000 : ℝ)*base92 + (1599441/400000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1727_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5431/1024 : ℝ) ≤ p) (hpb : p ≤ (5439/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (8023833/4000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (5333/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (6521/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4973/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17189/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1727_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1727_s2_0 (p : ℝ) (hpa : (5431/1024 : ℝ) ≤ p) (hpb : p ≤ (5439/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1352873871/10000000000 : ℝ)*x 0 + (54596871/100000000 : ℝ)*x 1 + (5139860591/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1352873871/10000000000 : ℝ)^5439 ≤ (8506758437533/100000000000000 : ℝ)^4415 := by
    have hnat : (1352873871 : ℕ)^5439*100000000000000^4415 ≤ 8506758437533^4415*10000000000^5439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1352873871 10000000000 8506758437533 100000000000000 5439 4415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (54596871/100000000 : ℝ)^5439 ≤ (47446845235931/100000000000000 : ℝ)^4415 := by
    have hnat : (54596871 : ℕ)^5439*100000000000000^4415 ≤ 47446845235931^4415*100000000^5439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      54596871 100000000 47446845235931 100000000000000 5439 4415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5139860591/10000000000 : ℝ)^5439 ≤ (44046396310723/100000000000000 : ℝ)^4415 := by
    have hnat : (5139860591 : ℕ)^5439*100000000000000^4415 ≤ 44046396310723^4415*10000000000^5439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5139860591 10000000000 44046396310723 100000000000000 5439 4415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5439/1024 : ℝ)) 5439 4415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1352873871/10000000000 : ℝ), (54596871/100000000 : ℝ), (5139860591/10000000000 : ℝ)] ![(8506758437533/100000000000000 : ℝ), (47446845235931/100000000000000 : ℝ), (44046396310723/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1352873871/10000000000 : ℝ)|^5439 ≤ (8506758437533/100000000000000 : ℝ)^4415
        have hw : |(-1352873871/10000000000 : ℝ)|=(1352873871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(54596871/100000000 : ℝ)|^5439 ≤ (47446845235931/100000000000000 : ℝ)^4415
        have hw : |(54596871/100000000 : ℝ)|=(54596871/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5139860591/10000000000 : ℝ)|^5439 ≤ (44046396310723/100000000000000 : ℝ)^4415
        have hw : |(5139860591/10000000000 : ℝ)|=(5139860591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1727_s2_1 (p : ℝ) (hpa : (5431/1024 : ℝ) ≤ p) (hpb : p ≤ (5439/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5337883141/10000000000 : ℝ)*x 0 + (-1518498003/10000000000 : ℝ)*x 1 + (5139859881/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5337883141/10000000000 : ℝ)^5439 ≤ (11536550808967/25000000000000 : ℝ)^4415 := by
    have hnat : (5337883141 : ℕ)^5439*25000000000000^4415 ≤ 11536550808967^4415*10000000000^5439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5337883141 10000000000 11536550808967 25000000000000 5439 4415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1518498003/10000000000 : ℝ)^5439 ≤ (9807407939521/100000000000000 : ℝ)^4415 := by
    have hnat : (1518498003 : ℕ)^5439*100000000000000^4415 ≤ 9807407939521^4415*10000000000^5439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1518498003 10000000000 9807407939521 100000000000000 5439 4415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5139859881/10000000000 : ℝ)^5439 ≤ (22023194407567/50000000000000 : ℝ)^4415 := by
    have hnat : (5139859881 : ℕ)^5439*50000000000000^4415 ≤ 22023194407567^4415*10000000000^5439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5139859881 10000000000 22023194407567 50000000000000 5439 4415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5439/1024 : ℝ)) 5439 4415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5337883141/10000000000 : ℝ), (-1518498003/10000000000 : ℝ), (5139859881/10000000000 : ℝ)] ![(11536550808967/25000000000000 : ℝ), (9807407939521/100000000000000 : ℝ), (22023194407567/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5337883141/10000000000 : ℝ)|^5439 ≤ (11536550808967/25000000000000 : ℝ)^4415
        have hw : |(5337883141/10000000000 : ℝ)|=(5337883141/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1518498003/10000000000 : ℝ)|^5439 ≤ (9807407939521/100000000000000 : ℝ)^4415
        have hw : |(-1518498003/10000000000 : ℝ)|=(1518498003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5139859881/10000000000 : ℝ)|^5439 ≤ (22023194407567/50000000000000 : ℝ)^4415
        have hw : |(5139859881/10000000000 : ℝ)|=(5139859881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1727_s2_2 (p : ℝ) (hpa : (5431/1024 : ℝ) ≤ p) (hpb : p ≤ (5439/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5337882299/10000000000 : ℝ)*x 0 + (1284965207/2500000000 : ℝ)*x 1 + (-759248937/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5337882299/10000000000 : ℝ)^5439 ≤ (11536548567113/25000000000000 : ℝ)^4415 := by
    have hnat : (5337882299 : ℕ)^5439*25000000000000^4415 ≤ 11536548567113^4415*10000000000^5439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5337882299 10000000000 11536548567113 25000000000000 5439 4415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1284965207/2500000000 : ℝ)^5439 ≤ (11011599703193/25000000000000 : ℝ)^4415 := by
    have hnat : (1284965207 : ℕ)^5439*25000000000000^4415 ≤ 11011599703193^4415*2500000000^5439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1284965207 2500000000 11011599703193 25000000000000 5439 4415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (759248937/5000000000 : ℝ)^5439 ≤ (4903703456559/50000000000000 : ℝ)^4415 := by
    have hnat : (759248937 : ℕ)^5439*50000000000000^4415 ≤ 4903703456559^4415*5000000000^5439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      759248937 5000000000 4903703456559 50000000000000 5439 4415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5439/1024 : ℝ)) 5439 4415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5337882299/10000000000 : ℝ), (1284965207/2500000000 : ℝ), (-759248937/5000000000 : ℝ)] ![(11536548567113/25000000000000 : ℝ), (11011599703193/25000000000000 : ℝ), (4903703456559/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5337882299/10000000000 : ℝ)|^5439 ≤ (11536548567113/25000000000000 : ℝ)^4415
        have hw : |(5337882299/10000000000 : ℝ)|=(5337882299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1284965207/2500000000 : ℝ)|^5439 ≤ (11011599703193/25000000000000 : ℝ)^4415
        have hw : |(1284965207/2500000000 : ℝ)|=(1284965207/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-759248937/5000000000 : ℝ)|^5439 ≤ (4903703456559/50000000000000 : ℝ)^4415
        have hw : |(-759248937/5000000000 : ℝ)|=(759248937/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1727_s2_3 (p : ℝ) (hpa : (5431/1024 : ℝ) ≤ p) (hpb : p ≤ (5439/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4083418649/10000000000 : ℝ)*x 0 + (113092853/312500000 : ℝ)*x 1 + (4582264101/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4083418649/10000000000 : ℝ)^5439 ≤ (2073414544937/6250000000000 : ℝ)^4415 := by
    have hnat : (4083418649 : ℕ)^5439*6250000000000^4415 ≤ 2073414544937^4415*10000000000^5439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4083418649 10000000000 2073414544937 6250000000000 5439 4415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (113092853/312500000 : ℝ)^5439 ≤ (28589389745711/100000000000000 : ℝ)^4415 := by
    have hnat : (113092853 : ℕ)^5439*100000000000000^4415 ≤ 28589389745711^4415*312500000^5439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      113092853 312500000 28589389745711 100000000000000 5439 4415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4582264101/10000000000 : ℝ)^5439 ≤ (19117988763989/50000000000000 : ℝ)^4415 := by
    have hnat : (4582264101 : ℕ)^5439*50000000000000^4415 ≤ 19117988763989^4415*10000000000^5439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4582264101 10000000000 19117988763989 50000000000000 5439 4415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5439/1024 : ℝ)) 5439 4415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4083418649/10000000000 : ℝ), (113092853/312500000 : ℝ), (4582264101/10000000000 : ℝ)] ![(2073414544937/6250000000000 : ℝ), (28589389745711/100000000000000 : ℝ), (19117988763989/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4083418649/10000000000 : ℝ)|^5439 ≤ (2073414544937/6250000000000 : ℝ)^4415
        have hw : |(4083418649/10000000000 : ℝ)|=(4083418649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(113092853/312500000 : ℝ)|^5439 ≤ (28589389745711/100000000000000 : ℝ)^4415
        have hw : |(113092853/312500000 : ℝ)|=(113092853/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4582264101/10000000000 : ℝ)|^5439 ≤ (19117988763989/50000000000000 : ℝ)^4415
        have hw : |(4582264101/10000000000 : ℝ)|=(4582264101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1727_s2_4 (p : ℝ) (hpa : (5431/1024 : ℝ) ≤ p) (hpb : p ≤ (5439/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-676508259/5000000000 : ℝ)*x 0 + (5143460837/10000000000 : ℝ)*x 1 + (8729653/16000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (676508259/5000000000 : ℝ)^5439 ≤ (2126965859903/25000000000000 : ℝ)^4415 := by
    have hnat : (676508259 : ℕ)^5439*25000000000000^4415 ≤ 2126965859903^4415*5000000000^5439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      676508259 5000000000 2126965859903 25000000000000 5439 4415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5143460837/10000000000 : ℝ)^5439 ≤ (44084407796027/100000000000000 : ℝ)^4415 := by
    have hnat : (5143460837 : ℕ)^5439*100000000000000^4415 ≤ 44084407796027^4415*10000000000^5439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5143460837 10000000000 44084407796027 100000000000000 5439 4415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8729653/16000000 : ℝ)^5439 ≤ (47407728753291/100000000000000 : ℝ)^4415 := by
    have hnat : (8729653 : ℕ)^5439*100000000000000^4415 ≤ 47407728753291^4415*16000000^5439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8729653 16000000 47407728753291 100000000000000 5439 4415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5439/1024 : ℝ)) 5439 4415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-676508259/5000000000 : ℝ), (5143460837/10000000000 : ℝ), (8729653/16000000 : ℝ)] ![(2126965859903/25000000000000 : ℝ), (44084407796027/100000000000000 : ℝ), (47407728753291/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-676508259/5000000000 : ℝ)|^5439 ≤ (2126965859903/25000000000000 : ℝ)^4415
        have hw : |(-676508259/5000000000 : ℝ)|=(676508259/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5143460837/10000000000 : ℝ)|^5439 ≤ (44084407796027/100000000000000 : ℝ)^4415
        have hw : |(5143460837/10000000000 : ℝ)|=(5143460837/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(8729653/16000000 : ℝ)|^5439 ≤ (47407728753291/100000000000000 : ℝ)^4415
        have hw : |(8729653/16000000 : ℝ)|=(8729653/16000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1727_s2_5 (p : ℝ) (hpa : (5431/1024 : ℝ) ≤ p) (hpb : p ≤ (5439/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5252279251/10000000000 : ℝ)*x 0 + (-300581221/2500000000 : ℝ)*x 1 + (5456033033/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5252279251/10000000000 : ℝ)^5439 ≤ (22618106251631/50000000000000 : ℝ)^4415 := by
    have hnat : (5252279251 : ℕ)^5439*50000000000000^4415 ≤ 22618106251631^4415*10000000000^5439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5252279251 10000000000 22618106251631 50000000000000 5439 4415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (300581221/2500000000 : ℝ)^5439 ≤ (183901493101/2500000000000 : ℝ)^4415 := by
    have hnat : (300581221 : ℕ)^5439*2500000000000^4415 ≤ 183901493101^4415*2500000000^5439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      300581221 2500000000 183901493101 2500000000000 5439 4415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5456033033/10000000000 : ℝ)^5439 ≤ (4740772776849/10000000000000 : ℝ)^4415 := by
    have hnat : (5456033033 : ℕ)^5439*10000000000000^4415 ≤ 4740772776849^4415*10000000000^5439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5456033033 10000000000 4740772776849 10000000000000 5439 4415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5439/1024 : ℝ)) 5439 4415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5252279251/10000000000 : ℝ), (-300581221/2500000000 : ℝ), (5456033033/10000000000 : ℝ)] ![(22618106251631/50000000000000 : ℝ), (183901493101/2500000000000 : ℝ), (4740772776849/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5252279251/10000000000 : ℝ)|^5439 ≤ (22618106251631/50000000000000 : ℝ)^4415
        have hw : |(5252279251/10000000000 : ℝ)|=(5252279251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-300581221/2500000000 : ℝ)|^5439 ≤ (183901493101/2500000000000 : ℝ)^4415
        have hw : |(-300581221/2500000000 : ℝ)|=(300581221/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5456033033/10000000000 : ℝ)|^5439 ≤ (4740772776849/10000000000000 : ℝ)^4415
        have hw : |(5456033033/10000000000 : ℝ)|=(5456033033/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1727_s2_6 (p : ℝ) (hpa : (5431/1024 : ℝ) ≤ p) (hpb : p ≤ (5439/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1050455841/2000000000 : ℝ)*x 0 + (272801657/500000000 : ℝ)*x 1 + (-300581199/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1050455841/2000000000 : ℝ)^5439 ≤ (45236212015189/100000000000000 : ℝ)^4415 := by
    have hnat : (1050455841 : ℕ)^5439*100000000000000^4415 ≤ 45236212015189^4415*2000000000^5439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1050455841 2000000000 45236212015189 100000000000000 5439 4415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (272801657/500000000 : ℝ)^5439 ≤ (740745764279/1562500000000 : ℝ)^4415 := by
    have hnat : (272801657 : ℕ)^5439*1562500000000^4415 ≤ 740745764279^4415*500000000^5439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      272801657 500000000 740745764279 1562500000000 5439 4415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (300581199/2500000000 : ℝ)^5439 ≤ (7356059060763/100000000000000 : ℝ)^4415 := by
    have hnat : (300581199 : ℕ)^5439*100000000000000^4415 ≤ 7356059060763^4415*2500000000^5439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      300581199 2500000000 7356059060763 100000000000000 5439 4415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5439/1024 : ℝ)) 5439 4415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1050455841/2000000000 : ℝ), (272801657/500000000 : ℝ), (-300581199/2500000000 : ℝ)] ![(45236212015189/100000000000000 : ℝ), (740745764279/1562500000000 : ℝ), (7356059060763/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1050455841/2000000000 : ℝ)|^5439 ≤ (45236212015189/100000000000000 : ℝ)^4415
        have hw : |(1050455841/2000000000 : ℝ)|=(1050455841/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(272801657/500000000 : ℝ)|^5439 ≤ (740745764279/1562500000000 : ℝ)^4415
        have hw : |(272801657/500000000 : ℝ)|=(272801657/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-300581199/2500000000 : ℝ)|^5439 ≤ (7356059060763/100000000000000 : ℝ)^4415
        have hw : |(-300581199/2500000000 : ℝ)|=(300581199/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1727_s2_7 (p : ℝ) (hpa : (5431/1024 : ℝ) ≤ p) (hpb : p ≤ (5439/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (510481041/1250000000 : ℝ)*x 0 + (4571419139/10000000000 : ℝ)*x 1 + (1814988761/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (510481041/1250000000 : ℝ)^5439 ≤ (6635786645863/20000000000000 : ℝ)^4415 := by
    have hnat : (510481041 : ℕ)^5439*20000000000000^4415 ≤ 6635786645863^4415*1250000000^5439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      510481041 1250000000 6635786645863 20000000000000 5439 4415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4571419139/10000000000 : ℝ)^5439 ≤ (38124525190971/100000000000000 : ℝ)^4415 := by
    have hnat : (4571419139 : ℕ)^5439*100000000000000^4415 ≤ 38124525190971^4415*10000000000^5439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4571419139 10000000000 38124525190971 100000000000000 5439 4415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1814988761/5000000000 : ℝ)^5439 ≤ (14348270782477/50000000000000 : ℝ)^4415 := by
    have hnat : (1814988761 : ℕ)^5439*50000000000000^4415 ≤ 14348270782477^4415*5000000000^5439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1814988761 5000000000 14348270782477 50000000000000 5439 4415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5439/1024 : ℝ)) 5439 4415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(510481041/1250000000 : ℝ), (4571419139/10000000000 : ℝ), (1814988761/5000000000 : ℝ)] ![(6635786645863/20000000000000 : ℝ), (38124525190971/100000000000000 : ℝ), (14348270782477/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(510481041/1250000000 : ℝ)|^5439 ≤ (6635786645863/20000000000000 : ℝ)^4415
        have hw : |(510481041/1250000000 : ℝ)|=(510481041/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4571419139/10000000000 : ℝ)|^5439 ≤ (38124525190971/100000000000000 : ℝ)^4415
        have hw : |(4571419139/10000000000 : ℝ)|=(4571419139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1814988761/5000000000 : ℝ)|^5439 ≤ (14348270782477/50000000000000 : ℝ)^4415
        have hw : |(1814988761/5000000000 : ℝ)|=(1814988761/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1727_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5431/1024 : ℝ) ≤ p) (hpb : p ≤ (5439/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (8023833/4000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17189/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4973/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (10129/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16977/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (17189/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4973/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (17189/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4973/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (17189/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4973/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (17189/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4973/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (17189/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4973/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (17189/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4973/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (4973/50000 : ℝ) ^ (5431/1024 : ℝ) ≤ (96571092079703/20000000000000000000 : ℝ) := by
    have hpowers : (4973/50000 : ℝ)^5431 ≤ (96571092079703/20000000000000000000 : ℝ)^1024 := by
      have hnat : (4973 : ℕ)^5431*20000000000000000000^1024 ≤ 96571092079703^1024*50000^5431 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4973 50000 96571092079703 20000000000000000000 5431 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4973/50000 : ℝ)) (X := (96571092079703/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5431 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (17189/100000 : ℝ) ^ (5431/1024 : ℝ) ≤ (1098753615680609/12500000000000000000 : ℝ) := by
    have hpowers : (17189/100000 : ℝ)^5431 ≤ (1098753615680609/12500000000000000000 : ℝ)^1024 := by
      have hnat : (17189 : ℕ)^5431*12500000000000000000^1024 ≤ 1098753615680609^1024*100000^5431 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17189 100000 1098753615680609 12500000000000000000 5431 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (17189/100000 : ℝ)) (X := (1098753615680609/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 5431 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000096571092079703/10000000000000000000 : ℝ) ≤ (10000018208140459/10000000000000000 : ℝ) ^ (5431/1024 : ℝ) := by
    have hpowers : (10000096571092079703/10000000000000000000 : ℝ)^1024 ≤ (10000018208140459/10000000000000000 : ℝ)^5431 := by
      have hnat : (10000096571092079703 : ℕ)^1024*10000000000000000^5431 ≤ 10000018208140459^5431*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000096571092079703 10000000000000000000 10000018208140459 10000000000000000 1024 5431 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000018208140459/10000000000000000 : ℝ)) (X := (10000096571092079703/10000000000000000000 : ℝ)) (by norm_num) 5431 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100009272884385843387/100000000000000000000 : ℝ) ≤ (10000174831087991/10000000000000000 : ℝ) ^ (5431/1024 : ℝ) := by
    have hpowers : (100009272884385843387/100000000000000000000 : ℝ)^1024 ≤ (10000174831087991/10000000000000000 : ℝ)^5431 := by
      have hnat : (100009272884385843387 : ℕ)^1024*10000000000000000^5431 ≤ 10000174831087991^5431*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100009272884385843387 100000000000000000000 10000174831087991 10000000000000000 1024 5431 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000174831087991/10000000000000000 : ℝ)) (X := (100009272884385843387/100000000000000000000 : ℝ)) (by norm_num) 5431 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (6251098753615680609/6250000000000000000 : ℝ) ≤ (10000331454035523/10000000000000000 : ℝ) ^ (5431/1024 : ℝ) := by
    have hpowers : (6251098753615680609/6250000000000000000 : ℝ)^1024 ≤ (10000331454035523/10000000000000000 : ℝ)^5431 := by
      have hnat : (6251098753615680609 : ℕ)^1024*10000000000000000^5431 ≤ 10000331454035523^5431*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6251098753615680609 6250000000000000000 10000331454035523 10000000000000000 1024 5431 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000331454035523/10000000000000000 : ℝ)) (X := (6251098753615680609/6250000000000000000 : ℝ)) (by norm_num) 5431 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(96571092079703/20000000000000000000 : ℝ) ≤ ((72427016337889037993/72430000000000000000 : ℝ)+2*(39155736883/181075000000000 : ℝ)*(4973/50000 : ℝ))^(5431/1024 : ℝ) := by
    rw [show (72427016337889037993/72430000000000000000 : ℝ)+2*(39155736883/181075000000000 : ℝ)*(4973/50000 : ℝ)=(10000018208140459/10000000000000000 : ℝ) by norm_num, show 1+2*(96571092079703/20000000000000000000 : ℝ)=(10000096571092079703/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1098753615680609/12500000000000000000 : ℝ)+(96571092079703/20000000000000000000 : ℝ) ≤ ((72427016337889037993/72430000000000000000 : ℝ)+(39155736883/181075000000000 : ℝ)*((17189/100000 : ℝ)+(4973/50000 : ℝ)))^(5431/1024 : ℝ) := by
    rw [show (72427016337889037993/72430000000000000000 : ℝ)+(39155736883/181075000000000 : ℝ)*((17189/100000 : ℝ)+(4973/50000 : ℝ))=(10000174831087991/10000000000000000 : ℝ) by norm_num, show 1+(1098753615680609/12500000000000000000 : ℝ)+(96571092079703/20000000000000000000 : ℝ)=(100009272884385843387/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1098753615680609/12500000000000000000 : ℝ) ≤ ((72427016337889037993/72430000000000000000 : ℝ)+2*(39155736883/181075000000000 : ℝ)*(17189/100000 : ℝ))^(5431/1024 : ℝ) := by
    rw [show (72427016337889037993/72430000000000000000 : ℝ)+2*(39155736883/181075000000000 : ℝ)*(17189/100000 : ℝ)=(10000331454035523/10000000000000000 : ℝ) by norm_num, show 1+2*(1098753615680609/12500000000000000000 : ℝ)=(6251098753615680609/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (72427016337889037993/72430000000000000000 : ℝ)*(X 1 0+X 2 0)+(39155736883/181075000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5431/1024 : ℝ)) (lo := (4973/50000 : ℝ)) (hi := (17189/100000 : ℝ)) (c := (72427016337889037993/72430000000000000000 : ℝ)) (alpha := (39155736883/181075000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (72427016337889037993/72430000000000000000 : ℝ)*(X 0 1+X 2 1)+(39155736883/181075000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5431/1024 : ℝ)) (lo := (4973/50000 : ℝ)) (hi := (17189/100000 : ℝ)) (c := (72427016337889037993/72430000000000000000 : ℝ)) (alpha := (39155736883/181075000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (72427016337889037993/72430000000000000000 : ℝ)*(X 0 2+X 1 2)+(39155736883/181075000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5431/1024 : ℝ)) (lo := (4973/50000 : ℝ)) (hi := (17189/100000 : ℝ)) (c := (72427016337889037993/72430000000000000000 : ℝ)) (alpha := (39155736883/181075000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1352873871/10000000000 : ℝ)*X 0 0+(54596871/100000000 : ℝ)*X 0 1+(5139860591/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1727_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5337883141/10000000000 : ℝ)*X 1 0+(-1518498003/10000000000 : ℝ)*X 1 1+(5139859881/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1727_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5337882299/10000000000 : ℝ)*X 2 0+(1284965207/2500000000 : ℝ)*X 2 1+(-759248937/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1727_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4083418649/10000000000 : ℝ)*X 0 0+(113092853/312500000 : ℝ)*X 0 1+(4582264101/10000000000 : ℝ)*X 0 2+(4083418649/10000000000 : ℝ)*X 1 0+(113092853/312500000 : ℝ)*X 1 1+(4582264101/10000000000 : ℝ)*X 1 2+(4083418649/10000000000 : ℝ)*X 2 0+(113092853/312500000 : ℝ)*X 2 1+(4582264101/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1727_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-676508259/5000000000 : ℝ)*X 0 0+(5143460837/10000000000 : ℝ)*X 0 1+(8729653/16000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1727_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5252279251/10000000000 : ℝ)*X 1 0+(-300581221/2500000000 : ℝ)*X 1 1+(5456033033/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1727_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1050455841/2000000000 : ℝ)*X 2 0+(272801657/500000000 : ℝ)*X 2 1+(-300581199/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1727_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((510481041/1250000000 : ℝ)*X 0 0+(4571419139/10000000000 : ℝ)*X 0 1+(1814988761/5000000000 : ℝ)*X 0 2+(510481041/1250000000 : ℝ)*X 1 0+(4571419139/10000000000 : ℝ)*X 1 1+(1814988761/5000000000 : ℝ)*X 1 2+(510481041/1250000000 : ℝ)*X 2 0+(4571419139/10000000000 : ℝ)*X 2 1+(1814988761/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1727_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (24624836037610768488483004827/1810750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (19288119/1000000000000 : ℝ)*(base19) + (16194163/1250000000000 : ℝ)*(base23) + (14953383/20000000000000 : ℝ)*(lower2) + (38255991/12500000000000 : ℝ)*(upper3) + (58376067/25000000000000 : ℝ)*(upper5) + (1041210148082971/50000000000000 : ℝ)*(major0) + (1041210148082971/50000000000000 : ℝ)*(major1) + (1041210148082971/50000000000000 : ℝ)*(major2) + (3126709724505689/100000000000000 : ℝ)*(sp0) + (781680185956457/25000000000000 : ℝ)*(sp1) + (195420086069043/6250000000000 : ℝ)*(sp2) + (259527889584091/25000000000000 : ℝ)*(sp3) + (12948132039/100000000000000 : ℝ)*(sp4) + (5908049561/100000000000000 : ℝ)*(sp7) + (259529366596481/25000000000000 : ℝ)*(f.failure) + (97710083519929/3125000000000 : ℝ)*(f.sum) + (53477150383699/36215000000000000000000000000 : ℝ)*base65 + (41497062317226482797/3621500000000000000000000000000000 : ℝ)*base68 + (38581415895527482797/3621500000000000000000000000000000 : ℝ)*base70 + (10167023001935482797/3621500000000000000000000000000000 : ℝ)*base72 + (62217835110241/36215000000000000000000000000 : ℝ)*base74 + (46855139680398482797/3621500000000000000000000000000000 : ℝ)*base76 + (13149516439561482797/3621500000000000000000000000000000 : ℝ)*base78 + (51981279904927982797/3621500000000000000000000000000000 : ℝ)*base80 + (5422868468533/18107500000000000000000000000 : ℝ)*base82 + (68327/100000000000000000000 : ℝ)*base90 + (68327/100000000000000000000 : ℝ)*base92 + (68327/100000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (20301037049806284602454080649/1810750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (104981671/6250000000000 : ℝ)*(base19) + (1816985667/100000000000000 : ℝ)*(base23) + (128208639/50000000000000 : ℝ)*(upper3) + (68297059/100000000000000 : ℝ)*(lower4) + (253575569/100000000000000 : ℝ)*(upper5) + (1065364964871269/50000000000000 : ℝ)*(major0) + (1065364964871269/50000000000000 : ℝ)*(major1) + (1065364964871269/50000000000000 : ℝ)*(major2) + (15099407641/100000000000000 : ℝ)*(sp1) + (8631642189/50000000000000 : ℝ)*(sp2) + (639851789814891/20000000000000 : ℝ)*(sp4) + (1599621084980039/50000000000000 : ℝ)*(sp5) + (319923986880441/10000000000000 : ℝ)*(sp6) + (53110026834869/5000000000000 : ℝ)*(sp7) + (53110026834869/5000000000000 : ℝ)*(f.failure) + (639851789814891/20000000000000 : ℝ)*(f.sum) + (72457053865983/18107500000000000000000000000 : ℝ)*base65 + (11032842665776576883/3621500000000000000000000000000000 : ℝ)*base68 + (35697763545253423117/3621500000000000000000000000000000 : ℝ)*base69 + (44033412235027423117/3621500000000000000000000000000000 : ℝ)*base71 + (103071762301959/36215000000000000000000000000 : ℝ)*base74 + (8226270703276576883/3621500000000000000000000000000000 : ℝ)*base76 + (23657052940297923117/3621500000000000000000000000000000 : ℝ)*base77 + (12307458476519923117/3621500000000000000000000000000000 : ℝ)*base79 + (29704424759549/9053750000000000000000000000 : ℝ)*base81 + (167123/20000000000000000000 : ℝ)*base90 + (167123/20000000000000000000 : ℝ)*base92 + (167123/20000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1727_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5431/1024 : ℝ) ≤ p) (hpb : p ≤ (5439/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (8023833/4000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17189/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4973/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10129/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16977/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1727_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1727_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5431/1024 : ℝ) ≤ p) (hpb : p ≤ (5439/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (8023833/4000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10129/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16977/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1727_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1727_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1727_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5431/1024 : ℝ) ≤ p) (hpb : p ≤ (5439/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (8023833/4000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10129/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16977/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1727_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
