-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1229_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:14:09.811436+00:00
-- url     : https://prove2.me/submissions/742cab8f-486c-42e8-a852-7e6a51d11978

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
theorem support_rectangle_w1229_s3_0 (p : ℝ) (hpa : (8421/2048 : ℝ) ≤ p) (hpb : p ≤ (4211/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2123009623/10000000000 : ℝ)*x 0 + (542080809/1000000000 : ℝ)*x 1 + (1309901371/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2123009623/10000000000 : ℝ)^4211 ≤ (12903218729141/100000000000000 : ℝ)^3187 := by
    have hnat : (2123009623 : ℕ)^4211*100000000000000^3187 ≤ 12903218729141^3187*10000000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2123009623 10000000000 12903218729141 100000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (542080809/1000000000 : ℝ)^4211 ≤ (44526380769587/100000000000000 : ℝ)^3187 := by
    have hnat : (542080809 : ℕ)^4211*100000000000000^3187 ≤ 44526380769587^3187*1000000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      542080809 1000000000 44526380769587 100000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1309901371/2500000000 : ℝ)^4211 ≤ (332581253779/781250000000 : ℝ)^3187 := by
    have hnat : (1309901371 : ℕ)^4211*781250000000^3187 ≤ 332581253779^3187*2500000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1309901371 2500000000 332581253779 781250000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4211/1024 : ℝ)) 4211 3187 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2123009623/10000000000 : ℝ), (542080809/1000000000 : ℝ), (1309901371/2500000000 : ℝ)] ![(12903218729141/100000000000000 : ℝ), (44526380769587/100000000000000 : ℝ), (332581253779/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2123009623/10000000000 : ℝ)|^4211 ≤ (12903218729141/100000000000000 : ℝ)^3187
        have hw : |(-2123009623/10000000000 : ℝ)|=(2123009623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(542080809/1000000000 : ℝ)|^4211 ≤ (44526380769587/100000000000000 : ℝ)^3187
        have hw : |(542080809/1000000000 : ℝ)|=(542080809/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1309901371/2500000000 : ℝ)|^4211 ≤ (332581253779/781250000000 : ℝ)^3187
        have hw : |(1309901371/2500000000 : ℝ)|=(1309901371/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1229_s3_1 (p : ℝ) (hpa : (8421/2048 : ℝ) ≤ p) (hpb : p ≤ (4211/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5351777459/10000000000 : ℝ)*x 0 + (-1107735163/5000000000 : ℝ)*x 1 + (5239605661/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5351777459/10000000000 : ℝ)^4211 ≤ (8755743374197/20000000000000 : ℝ)^3187 := by
    have hnat : (5351777459 : ℕ)^4211*20000000000000^3187 ≤ 8755743374197^3187*10000000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5351777459 10000000000 8755743374197 20000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1107735163/5000000000 : ℝ)^4211 ≤ (6825440367317/50000000000000 : ℝ)^3187 := by
    have hnat : (1107735163 : ℕ)^4211*50000000000000^3187 ≤ 6825440367317^3187*5000000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1107735163 5000000000 6825440367317 50000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5239605661/10000000000 : ℝ)^4211 ≤ (10642600595963/25000000000000 : ℝ)^3187 := by
    have hnat : (5239605661 : ℕ)^4211*25000000000000^3187 ≤ 10642600595963^3187*10000000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5239605661 10000000000 10642600595963 25000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4211/1024 : ℝ)) 4211 3187 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5351777459/10000000000 : ℝ), (-1107735163/5000000000 : ℝ), (5239605661/10000000000 : ℝ)] ![(8755743374197/20000000000000 : ℝ), (6825440367317/50000000000000 : ℝ), (10642600595963/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5351777459/10000000000 : ℝ)|^4211 ≤ (8755743374197/20000000000000 : ℝ)^3187
        have hw : |(5351777459/10000000000 : ℝ)|=(5351777459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1107735163/5000000000 : ℝ)|^4211 ≤ (6825440367317/50000000000000 : ℝ)^3187
        have hw : |(-1107735163/5000000000 : ℝ)|=(1107735163/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5239605661/10000000000 : ℝ)|^4211 ≤ (10642600595963/25000000000000 : ℝ)^3187
        have hw : |(5239605661/10000000000 : ℝ)|=(5239605661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1229_s3_2 (p : ℝ) (hpa : (8421/2048 : ℝ) ≤ p) (hpb : p ≤ (4211/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5351777341/10000000000 : ℝ)*x 0 + (1047921213/2000000000 : ℝ)*x 1 + (-2215469949/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5351777341/10000000000 : ℝ)^4211 ≤ (21889357797787/50000000000000 : ℝ)^3187 := by
    have hnat : (5351777341 : ℕ)^4211*50000000000000^3187 ≤ 21889357797787^3187*10000000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5351777341 10000000000 21889357797787 50000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1047921213/2000000000 : ℝ)^4211 ≤ (8514081344179/20000000000000 : ℝ)^3187 := by
    have hnat : (1047921213 : ℕ)^4211*20000000000000^3187 ≤ 8514081344179^3187*2000000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1047921213 2000000000 8514081344179 20000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2215469949/10000000000 : ℝ)^4211 ≤ (2730175533067/20000000000000 : ℝ)^3187 := by
    have hnat : (2215469949 : ℕ)^4211*20000000000000^3187 ≤ 2730175533067^3187*10000000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2215469949 10000000000 2730175533067 20000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4211/1024 : ℝ)) 4211 3187 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5351777341/10000000000 : ℝ), (1047921213/2000000000 : ℝ), (-2215469949/10000000000 : ℝ)] ![(21889357797787/50000000000000 : ℝ), (8514081344179/20000000000000 : ℝ), (2730175533067/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5351777341/10000000000 : ℝ)|^4211 ≤ (21889357797787/50000000000000 : ℝ)^3187
        have hw : |(5351777341/10000000000 : ℝ)|=(5351777341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1047921213/2000000000 : ℝ)|^4211 ≤ (8514081344179/20000000000000 : ℝ)^3187
        have hw : |(1047921213/2000000000 : ℝ)|=(1047921213/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2215469949/10000000000 : ℝ)|^4211 ≤ (2730175533067/20000000000000 : ℝ)^3187
        have hw : |(-2215469949/10000000000 : ℝ)|=(2215469949/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1229_s3_3 (p : ℝ) (hpa : (8421/2048 : ℝ) ≤ p) (hpb : p ≤ (4211/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2175398273/5000000000 : ℝ)*x 0 + (2085614933/5000000000 : ℝ)*x 1 + (4537888473/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2175398273/5000000000 : ℝ)^4211 ≤ (6659919834373/20000000000000 : ℝ)^3187 := by
    have hnat : (2175398273 : ℕ)^4211*20000000000000^3187 ≤ 6659919834373^3187*5000000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2175398273 5000000000 6659919834373 20000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2085614933/5000000000 : ℝ)^4211 ≤ (31495823828323/100000000000000 : ℝ)^3187 := by
    have hnat : (2085614933 : ℕ)^4211*100000000000000^3187 ≤ 31495823828323^3187*5000000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2085614933 5000000000 31495823828323 100000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4537888473/10000000000 : ℝ)^4211 ≤ (35204576982319/100000000000000 : ℝ)^3187 := by
    have hnat : (4537888473 : ℕ)^4211*100000000000000^3187 ≤ 35204576982319^3187*10000000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4537888473 10000000000 35204576982319 100000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4211/1024 : ℝ)) 4211 3187 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2175398273/5000000000 : ℝ), (2085614933/5000000000 : ℝ), (4537888473/10000000000 : ℝ)] ![(6659919834373/20000000000000 : ℝ), (31495823828323/100000000000000 : ℝ), (35204576982319/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2175398273/5000000000 : ℝ)|^4211 ≤ (6659919834373/20000000000000 : ℝ)^3187
        have hw : |(2175398273/5000000000 : ℝ)|=(2175398273/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2085614933/5000000000 : ℝ)|^4211 ≤ (31495823828323/100000000000000 : ℝ)^3187
        have hw : |(2085614933/5000000000 : ℝ)|=(2085614933/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4537888473/10000000000 : ℝ)|^4211 ≤ (35204576982319/100000000000000 : ℝ)^3187
        have hw : |(4537888473/10000000000 : ℝ)|=(4537888473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1229_s3_4 (p : ℝ) (hpa : (8421/2048 : ℝ) ≤ p) (hpb : p ≤ (4211/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1061512147/5000000000 : ℝ)*x 0 + (2620134811/5000000000 : ℝ)*x 1 + (2710070143/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1061512147/5000000000 : ℝ)^4211 ≤ (1612917068319/12500000000000 : ℝ)^3187 := by
    have hnat : (1061512147 : ℕ)^4211*12500000000000^3187 ≤ 1612917068319^3187*5000000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061512147 5000000000 1612917068319 12500000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2620134811/5000000000 : ℝ)^4211 ≤ (8515506063807/20000000000000 : ℝ)^3187 := by
    have hnat : (2620134811 : ℕ)^4211*20000000000000^3187 ≤ 8515506063807^3187*5000000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2620134811 5000000000 8515506063807 20000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2710070143/5000000000 : ℝ)^4211 ≤ (5564891640471/12500000000000 : ℝ)^3187 := by
    have hnat : (2710070143 : ℕ)^4211*12500000000000^3187 ≤ 5564891640471^3187*5000000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2710070143 5000000000 5564891640471 12500000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4211/1024 : ℝ)) 4211 3187 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1061512147/5000000000 : ℝ), (2620134811/5000000000 : ℝ), (2710070143/5000000000 : ℝ)] ![(1612917068319/12500000000000 : ℝ), (8515506063807/20000000000000 : ℝ), (5564891640471/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1061512147/5000000000 : ℝ)|^4211 ≤ (1612917068319/12500000000000 : ℝ)^3187
        have hw : |(-1061512147/5000000000 : ℝ)|=(1061512147/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2620134811/5000000000 : ℝ)|^4211 ≤ (8515506063807/20000000000000 : ℝ)^3187
        have hw : |(2620134811/5000000000 : ℝ)|=(2620134811/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2710070143/5000000000 : ℝ)|^4211 ≤ (5564891640471/12500000000000 : ℝ)^3187
        have hw : |(2710070143/5000000000 : ℝ)|=(2710070143/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1229_s3_5 (p : ℝ) (hpa : (8421/2048 : ℝ) ≤ p) (hpb : p ≤ (4211/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305588423/10000000000 : ℝ)*x 0 + (-2034935997/10000000000 : ℝ)*x 1 + (5420140497/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305588423/10000000000 : ℝ)^4211 ≤ (43280173096281/100000000000000 : ℝ)^3187 := by
    have hnat : (5305588423 : ℕ)^4211*100000000000000^3187 ≤ 43280173096281^3187*10000000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305588423 10000000000 43280173096281 100000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2034935997/10000000000 : ℝ)^4211 ≤ (2440138295057/20000000000000 : ℝ)^3187 := by
    have hnat : (2034935997 : ℕ)^4211*20000000000000^3187 ≤ 2440138295057^3187*10000000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2034935997 10000000000 2440138295057 20000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5420140497/10000000000 : ℝ)^4211 ≤ (695611490839/1562500000000 : ℝ)^3187 := by
    have hnat : (5420140497 : ℕ)^4211*1562500000000^3187 ≤ 695611490839^3187*10000000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5420140497 10000000000 695611490839 1562500000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4211/1024 : ℝ)) 4211 3187 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305588423/10000000000 : ℝ), (-2034935997/10000000000 : ℝ), (5420140497/10000000000 : ℝ)] ![(43280173096281/100000000000000 : ℝ), (2440138295057/20000000000000 : ℝ), (695611490839/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305588423/10000000000 : ℝ)|^4211 ≤ (43280173096281/100000000000000 : ℝ)^3187
        have hw : |(5305588423/10000000000 : ℝ)|=(5305588423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2034935997/10000000000 : ℝ)|^4211 ≤ (2440138295057/20000000000000 : ℝ)^3187
        have hw : |(-2034935997/10000000000 : ℝ)|=(2034935997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5420140497/10000000000 : ℝ)|^4211 ≤ (695611490839/1562500000000 : ℝ)^3187
        have hw : |(5420140497/10000000000 : ℝ)|=(5420140497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1229_s3_6 (p : ℝ) (hpa : (8421/2048 : ℝ) ≤ p) (hpb : p ≤ (4211/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305588899/10000000000 : ℝ)*x 0 + (5420140451/10000000000 : ℝ)*x 1 + (-508733853/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305588899/10000000000 : ℝ)^4211 ≤ (865603564537/2000000000000 : ℝ)^3187 := by
    have hnat : (5305588899 : ℕ)^4211*2000000000000^3187 ≤ 865603564537^3187*10000000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305588899 10000000000 865603564537 2000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5420140451/10000000000 : ℝ)^4211 ≤ (4451913491447/10000000000000 : ℝ)^3187 := by
    have hnat : (5420140451 : ℕ)^4211*10000000000000^3187 ≤ 4451913491447^3187*10000000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5420140451 10000000000 4451913491447 10000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (508733853/2500000000 : ℝ)^4211 ≤ (12200686840893/100000000000000 : ℝ)^3187 := by
    have hnat : (508733853 : ℕ)^4211*100000000000000^3187 ≤ 12200686840893^3187*2500000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      508733853 2500000000 12200686840893 100000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4211/1024 : ℝ)) 4211 3187 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305588899/10000000000 : ℝ), (5420140451/10000000000 : ℝ), (-508733853/2500000000 : ℝ)] ![(865603564537/2000000000000 : ℝ), (4451913491447/10000000000000 : ℝ), (12200686840893/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305588899/10000000000 : ℝ)|^4211 ≤ (865603564537/2000000000000 : ℝ)^3187
        have hw : |(5305588899/10000000000 : ℝ)|=(5305588899/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5420140451/10000000000 : ℝ)|^4211 ≤ (4451913491447/10000000000000 : ℝ)^3187
        have hw : |(5420140451/10000000000 : ℝ)|=(5420140451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-508733853/2500000000 : ℝ)|^4211 ≤ (12200686840893/100000000000000 : ℝ)^3187
        have hw : |(-508733853/2500000000 : ℝ)|=(508733853/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1229_s3_7 (p : ℝ) (hpa : (8421/2048 : ℝ) ≤ p) (hpb : p ≤ (4211/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2175412917/5000000000 : ℝ)*x 0 + (453654539/1000000000 : ℝ)*x 1 + (208628999/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2175412917/5000000000 : ℝ)^4211 ≤ (33299895357229/100000000000000 : ℝ)^3187 := by
    have hnat : (2175412917 : ℕ)^4211*100000000000000^3187 ≤ 33299895357229^3187*5000000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2175412917 5000000000 33299895357229 100000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (453654539/1000000000 : ℝ)^4211 ≤ (35190810255637/100000000000000 : ℝ)^3187 := by
    have hnat : (453654539 : ℕ)^4211*100000000000000^3187 ≤ 35190810255637^3187*1000000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      453654539 1000000000 35190810255637 100000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (208628999/500000000 : ℝ)^4211 ≤ (7877323592411/25000000000000 : ℝ)^3187 := by
    have hnat : (208628999 : ℕ)^4211*25000000000000^3187 ≤ 7877323592411^3187*500000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      208628999 500000000 7877323592411 25000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4211/1024 : ℝ)) 4211 3187 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2175412917/5000000000 : ℝ), (453654539/1000000000 : ℝ), (208628999/500000000 : ℝ)] ![(33299895357229/100000000000000 : ℝ), (35190810255637/100000000000000 : ℝ), (7877323592411/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2175412917/5000000000 : ℝ)|^4211 ≤ (33299895357229/100000000000000 : ℝ)^3187
        have hw : |(2175412917/5000000000 : ℝ)|=(2175412917/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(453654539/1000000000 : ℝ)|^4211 ≤ (35190810255637/100000000000000 : ℝ)^3187
        have hw : |(453654539/1000000000 : ℝ)|=(453654539/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(208628999/500000000 : ℝ)|^4211 ≤ (7877323592411/25000000000000 : ℝ)^3187
        have hw : |(208628999/500000000 : ℝ)|=(208628999/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1229_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8421/2048 : ℝ) ≤ p) (hpb : p ≤ (4211/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151173987/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16257/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4723/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (10877/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14713/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16257/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4723/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16257/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4723/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16257/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4723/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16257/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4723/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16257/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4723/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16257/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4723/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (4723/50000 : ℝ) ^ (8421/2048 : ℝ) ≤ (23887335380987/390625000000000000 : ℝ) := by
    have hpowers : (4723/50000 : ℝ)^8421 ≤ (23887335380987/390625000000000000 : ℝ)^2048 := by
      have hnat : (4723 : ℕ)^8421*390625000000000000^2048 ≤ 23887335380987^2048*50000^8421 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4723 50000 23887335380987 390625000000000000 8421 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4723/50000 : ℝ)) (X := (23887335380987/390625000000000000 : ℝ)) (by norm_num) (by norm_num) 8421 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (16257/100000 : ℝ) ^ (8421/2048 : ℝ) ≤ (14252235998572269/25000000000000000000 : ℝ) := by
    have hpowers : (16257/100000 : ℝ)^8421 ≤ (14252235998572269/25000000000000000000 : ℝ)^2048 := by
      have hnat : (16257 : ℕ)^8421*25000000000000000000^2048 ≤ 14252235998572269^2048*100000^8421 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16257 100000 14252235998572269 25000000000000000000 8421 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16257/100000 : ℝ)) (X := (14252235998572269/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8421 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (195336387335380987/195312500000000000 : ℝ) ≤ (100002974293727/100000000000000 : ℝ) ^ (8421/2048 : ℝ) := by
    have hpowers : (195336387335380987/195312500000000000 : ℝ)^2048 ≤ (100002974293727/100000000000000 : ℝ)^8421 := by
      have hnat : (195336387335380987 : ℕ)^2048*100000000000000^8421 ≤ 100002974293727^8421*195312500000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        195336387335380987 195312500000000000 100002974293727 100000000000000 2048 8421 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (100002974293727/100000000000000 : ℝ)) (X := (195336387335380987/195312500000000000 : ℝ)) (by norm_num) 8421 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (25015781025462955437/25000000000000000000 : ℝ) ≤ (78136990790553/78125000000000 : ℝ) ^ (8421/2048 : ℝ) := by
    have hpowers : (25015781025462955437/25000000000000000000 : ℝ)^2048 ≤ (78136990790553/78125000000000 : ℝ)^8421 := by
      have hnat : (25015781025462955437 : ℕ)^2048*78125000000000^8421 ≤ 78136990790553^8421*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25015781025462955437 25000000000000000000 78136990790553 78125000000000 2048 8421 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (78136990790553/78125000000000 : ℝ)) (X := (25015781025462955437/25000000000000000000 : ℝ)) (by norm_num) 8421 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (12514252235998572269/12500000000000000000 : ℝ) ≤ (2500693053252217/2500000000000000 : ℝ) ^ (8421/2048 : ℝ) := by
    have hpowers : (12514252235998572269/12500000000000000000 : ℝ)^2048 ≤ (2500693053252217/2500000000000000 : ℝ)^8421 := by
      have hnat : (12514252235998572269 : ℕ)^2048*2500000000000000^8421 ≤ 2500693053252217^8421*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12514252235998572269 12500000000000000000 2500693053252217 2500000000000000 2048 8421 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500693053252217/2500000000000000 : ℝ)) (X := (12514252235998572269/12500000000000000000 : ℝ)) (by norm_num) 8421 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(23887335380987/390625000000000000 : ℝ) ≤ ((17022162246307554193/17027500000000000000 : ℝ)+2*(309347954521/170275000000000 : ℝ)*(4723/50000 : ℝ))^(8421/2048 : ℝ) := by
    rw [show (17022162246307554193/17027500000000000000 : ℝ)+2*(309347954521/170275000000000 : ℝ)*(4723/50000 : ℝ)=(100002974293727/100000000000000 : ℝ) by norm_num, show 1+2*(23887335380987/390625000000000000 : ℝ)=(195336387335380987/195312500000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(14252235998572269/25000000000000000000 : ℝ)+(23887335380987/390625000000000000 : ℝ) ≤ ((17022162246307554193/17027500000000000000 : ℝ)+(309347954521/170275000000000 : ℝ)*((16257/100000 : ℝ)+(4723/50000 : ℝ)))^(8421/2048 : ℝ) := by
    rw [show (17022162246307554193/17027500000000000000 : ℝ)+(309347954521/170275000000000 : ℝ)*((16257/100000 : ℝ)+(4723/50000 : ℝ))=(78136990790553/78125000000000 : ℝ) by norm_num, show 1+(14252235998572269/25000000000000000000 : ℝ)+(23887335380987/390625000000000000 : ℝ)=(25015781025462955437/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(14252235998572269/25000000000000000000 : ℝ) ≤ ((17022162246307554193/17027500000000000000 : ℝ)+2*(309347954521/170275000000000 : ℝ)*(16257/100000 : ℝ))^(8421/2048 : ℝ) := by
    rw [show (17022162246307554193/17027500000000000000 : ℝ)+2*(309347954521/170275000000000 : ℝ)*(16257/100000 : ℝ)=(2500693053252217/2500000000000000 : ℝ) by norm_num, show 1+2*(14252235998572269/25000000000000000000 : ℝ)=(12514252235998572269/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (17022162246307554193/17027500000000000000 : ℝ)*(X 1 0+X 2 0)+(309347954521/170275000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8421/2048 : ℝ)) (lo := (4723/50000 : ℝ)) (hi := (16257/100000 : ℝ)) (c := (17022162246307554193/17027500000000000000 : ℝ)) (alpha := (309347954521/170275000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (17022162246307554193/17027500000000000000 : ℝ)*(X 0 1+X 2 1)+(309347954521/170275000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8421/2048 : ℝ)) (lo := (4723/50000 : ℝ)) (hi := (16257/100000 : ℝ)) (c := (17022162246307554193/17027500000000000000 : ℝ)) (alpha := (309347954521/170275000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (17022162246307554193/17027500000000000000 : ℝ)*(X 0 2+X 1 2)+(309347954521/170275000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8421/2048 : ℝ)) (lo := (4723/50000 : ℝ)) (hi := (16257/100000 : ℝ)) (c := (17022162246307554193/17027500000000000000 : ℝ)) (alpha := (309347954521/170275000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2123009623/10000000000 : ℝ)*X 0 0+(542080809/1000000000 : ℝ)*X 0 1+(1309901371/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1229_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5351777459/10000000000 : ℝ)*X 1 0+(-1107735163/5000000000 : ℝ)*X 1 1+(5239605661/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1229_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5351777341/10000000000 : ℝ)*X 2 0+(1047921213/2000000000 : ℝ)*X 2 1+(-2215469949/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1229_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2175398273/5000000000 : ℝ)*X 0 0+(2085614933/5000000000 : ℝ)*X 0 1+(4537888473/10000000000 : ℝ)*X 0 2+(2175398273/5000000000 : ℝ)*X 1 0+(2085614933/5000000000 : ℝ)*X 1 1+(4537888473/10000000000 : ℝ)*X 1 2+(2175398273/5000000000 : ℝ)*X 2 0+(2085614933/5000000000 : ℝ)*X 2 1+(4537888473/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1229_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1061512147/5000000000 : ℝ)*X 0 0+(2620134811/5000000000 : ℝ)*X 0 1+(2710070143/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1229_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305588423/10000000000 : ℝ)*X 1 0+(-2034935997/10000000000 : ℝ)*X 1 1+(5420140497/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1229_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305588899/10000000000 : ℝ)*X 2 0+(5420140451/10000000000 : ℝ)*X 2 1+(-508733853/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1229_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2175412917/5000000000 : ℝ)*X 0 0+(453654539/1000000000 : ℝ)*X 0 1+(208628999/500000000 : ℝ)*X 0 2+(2175412917/5000000000 : ℝ)*X 1 0+(453654539/1000000000 : ℝ)*X 1 1+(208628999/500000000 : ℝ)*X 1 2+(2175412917/5000000000 : ℝ)*X 2 0+(453654539/1000000000 : ℝ)*X 2 1+(208628999/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1229_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (183239301380944832830901253/15203125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1933369683/100000000000000 : ℝ)*(base19) + (183150333/12500000000000 : ℝ)*(base23) + (185430987/100000000000000 : ℝ)*(lower2) + (8068491/10000000000000 : ℝ)*(upper3) + (5657589/2500000000000 : ℝ)*(upper5) + (1030768925736899/25000000000000 : ℝ)*(major0) + (1030768925736899/25000000000000 : ℝ)*(major1) + (1030768925736899/25000000000000 : ℝ)*(major2) + (1379681984036343/25000000000000 : ℝ)*(sp0) + (551877792393947/10000000000000 : ℝ)*(sp1) + (5518778392106489/100000000000000 : ℝ)*(sp2) + (545470481158473/20000000000000 : ℝ)*(sp3) + (2596058189/5000000000000 : ℝ)*(sp4) + (18741035691/100000000000000 : ℝ)*(sp7) + (340921393353507/12500000000000 : ℝ)*(f.failure) + (5518779857309153/100000000000000 : ℝ)*(f.sum) + (19250428349031/8513750000000000000000000000 : ℝ)*base65 + (1265767757336082493/425687500000000000000000000000000 : ℝ)*base68 + (1400965142302519993/425687500000000000000000000000000 : ℝ)*base70 + (5079323746788207493/425687500000000000000000000000000 : ℝ)*base72 + (5662515408283/4256875000000000000000000000 : ℝ)*base73 + (6295894001650144993/425687500000000000000000000000000 : ℝ)*base76 + (3833355454561230007/425687500000000000000000000000000 : ℝ)*base77 + (8381519628748269993/425687500000000000000000000000000 : ℝ)*base80 + (21031096379239/8513750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (3622409/1250000000000000000000 : ℝ)*base89 + (3622409/1250000000000000000000 : ℝ)*base91 + (3622409/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (309990717648916202032146399/30406250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (857031151/100000000000000 : ℝ)*(base19) + (1720722069/100000000000000 : ℝ)*(base23) + (274279597/100000000000000 : ℝ)*(upper3) + (794563/1250000000000 : ℝ)*(lower4) + (93256891/100000000000000 : ℝ)*(upper5) + (1038383356498183/25000000000000 : ℝ)*(major0) + (1038383356498183/25000000000000 : ℝ)*(major1) + (1038383356498183/25000000000000 : ℝ)*(major2) + (1304651753/10000000000000 : ℝ)*(sp1) + (1287524637/3125000000000 : ℝ)*(sp2) + (5559547902359109/100000000000000 : ℝ)*(sp4) + (5559533998810427/100000000000000 : ℝ)*(sp5) + (347469061303041/6250000000000 : ℝ)*(sp6) + (42929978278033/1562500000000 : ℝ)*(sp7) + (42929978278033/1562500000000 : ℝ)*(f.failure) + (5559547902359109/100000000000000 : ℝ)*(f.sum) + (100261837806289/17027500000000000000000000000 : ℝ)*base65 + (1414674881159206319/425687500000000000000000000000000 : ℝ)*base67 + (1156823471204293681/425687500000000000000000000000000 : ℝ)*base70 + (202145830982268819/425687500000000000000000000000000 : ℝ)*base71 + (213594229161533/34055000000000000000000000000 : ℝ)*base73 + (2843645314537893819/425687500000000000000000000000000 : ℝ)*base75 + (3601216093478168681/425687500000000000000000000000000 : ℝ)*base78 + (1731877616871831319/425687500000000000000000000000000 : ℝ)*base79 + (7649447673033/2128437500000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (622429/156250000000000000000 : ℝ)*base90 + (622429/156250000000000000000 : ℝ)*base92 + (622429/156250000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1229_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8421/2048 : ℝ) ≤ p) (hpb : p ≤ (4211/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151173987/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16257/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4723/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10877/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14713/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1229_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1229_s4_0 (p : ℝ) (hpa : (8421/2048 : ℝ) ≤ p) (hpb : p ≤ (4211/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2125383029/10000000000 : ℝ)*x 0 + (1349507217/2500000000 : ℝ)*x 1 + (2630414889/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2125383029/10000000000 : ℝ)^4211 ≤ (6461141040927/50000000000000 : ℝ)^3187 := by
    have hnat : (2125383029 : ℕ)^4211*50000000000000^3187 ≤ 6461141040927^3187*10000000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2125383029 10000000000 6461141040927 50000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1349507217/2500000000 : ℝ)^4211 ≤ (44279321097023/100000000000000 : ℝ)^3187 := by
    have hnat : (1349507217 : ℕ)^4211*100000000000000^3187 ≤ 44279321097023^3187*2500000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1349507217 2500000000 44279321097023 100000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2630414889/5000000000 : ℝ)^4211 ≤ (21399198405443/50000000000000 : ℝ)^3187 := by
    have hnat : (2630414889 : ℕ)^4211*50000000000000^3187 ≤ 21399198405443^3187*5000000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2630414889 5000000000 21399198405443 50000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4211/1024 : ℝ)) 4211 3187 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2125383029/10000000000 : ℝ), (1349507217/2500000000 : ℝ), (2630414889/5000000000 : ℝ)] ![(6461141040927/50000000000000 : ℝ), (44279321097023/100000000000000 : ℝ), (21399198405443/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2125383029/10000000000 : ℝ)|^4211 ≤ (6461141040927/50000000000000 : ℝ)^3187
        have hw : |(-2125383029/10000000000 : ℝ)|=(2125383029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1349507217/2500000000 : ℝ)|^4211 ≤ (44279321097023/100000000000000 : ℝ)^3187
        have hw : |(1349507217/2500000000 : ℝ)|=(1349507217/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2630414889/5000000000 : ℝ)|^4211 ≤ (21399198405443/50000000000000 : ℝ)^3187
        have hw : |(2630414889/5000000000 : ℝ)|=(2630414889/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1229_s4_1 (p : ℝ) (hpa : (8421/2048 : ℝ) ≤ p) (hpb : p ≤ (4211/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5346041713/10000000000 : ℝ)*x 0 + (-548762283/2500000000 : ℝ)*x 1 + (5260829781/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5346041713/10000000000 : ℝ)^4211 ≤ (10929183086747/25000000000000 : ℝ)^3187 := by
    have hnat : (5346041713 : ℕ)^4211*25000000000000^3187 ≤ 10929183086747^3187*10000000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5346041713 10000000000 10929183086747 25000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (548762283/2500000000 : ℝ)^4211 ≤ (3371217697397/25000000000000 : ℝ)^3187 := by
    have hnat : (548762283 : ℕ)^4211*25000000000000^3187 ≤ 3371217697397^3187*2500000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      548762283 2500000000 3371217697397 25000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5260829781/10000000000 : ℝ)^4211 ≤ (42798396843133/100000000000000 : ℝ)^3187 := by
    have hnat : (5260829781 : ℕ)^4211*100000000000000^3187 ≤ 42798396843133^3187*10000000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5260829781 10000000000 42798396843133 100000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4211/1024 : ℝ)) 4211 3187 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5346041713/10000000000 : ℝ), (-548762283/2500000000 : ℝ), (5260829781/10000000000 : ℝ)] ![(10929183086747/25000000000000 : ℝ), (3371217697397/25000000000000 : ℝ), (42798396843133/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5346041713/10000000000 : ℝ)|^4211 ≤ (10929183086747/25000000000000 : ℝ)^3187
        have hw : |(5346041713/10000000000 : ℝ)|=(5346041713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-548762283/2500000000 : ℝ)|^4211 ≤ (3371217697397/25000000000000 : ℝ)^3187
        have hw : |(-548762283/2500000000 : ℝ)|=(548762283/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5260829781/10000000000 : ℝ)|^4211 ≤ (42798396843133/100000000000000 : ℝ)^3187
        have hw : |(5260829781/10000000000 : ℝ)|=(5260829781/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1229_s4_2 (p : ℝ) (hpa : (8421/2048 : ℝ) ≤ p) (hpb : p ≤ (4211/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (534604173/1000000000 : ℝ)*x 0 + (5260829793/10000000000 : ℝ)*x 1 + (-439009819/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534604173/1000000000 : ℝ)^4211 ≤ (4371673253067/10000000000000 : ℝ)^3187 := by
    have hnat : (534604173 : ℕ)^4211*10000000000000^3187 ≤ 4371673253067^3187*1000000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534604173 1000000000 4371673253067 10000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5260829793/10000000000 : ℝ)^4211 ≤ (10699599243031/25000000000000 : ℝ)^3187 := by
    have hnat : (5260829793 : ℕ)^4211*25000000000000^3187 ≤ 10699599243031^3187*10000000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5260829793 10000000000 10699599243031 25000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (439009819/2000000000 : ℝ)^4211 ≤ (3371217622313/25000000000000 : ℝ)^3187 := by
    have hnat : (439009819 : ℕ)^4211*25000000000000^3187 ≤ 3371217622313^3187*2000000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      439009819 2000000000 3371217622313 25000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4211/1024 : ℝ)) 4211 3187 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(534604173/1000000000 : ℝ), (5260829793/10000000000 : ℝ), (-439009819/2000000000 : ℝ)] ![(4371673253067/10000000000000 : ℝ), (10699599243031/25000000000000 : ℝ), (3371217622313/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(534604173/1000000000 : ℝ)|^4211 ≤ (4371673253067/10000000000000 : ℝ)^3187
        have hw : |(534604173/1000000000 : ℝ)|=(534604173/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5260829793/10000000000 : ℝ)|^4211 ≤ (10699599243031/25000000000000 : ℝ)^3187
        have hw : |(5260829793/10000000000 : ℝ)|=(5260829793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-439009819/2000000000 : ℝ)|^4211 ≤ (3371217622313/25000000000000 : ℝ)^3187
        have hw : |(-439009819/2000000000 : ℝ)|=(439009819/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1229_s4_3 (p : ℝ) (hpa : (8421/2048 : ℝ) ≤ p) (hpb : p ≤ (4211/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (544027393/1250000000 : ℝ)*x 0 + (2107783733/5000000000 : ℝ)*x 1 + (4493187033/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (544027393/1250000000 : ℝ)^4211 ≤ (2082124152657/6250000000000 : ℝ)^3187 := by
    have hnat : (544027393 : ℕ)^4211*6250000000000^3187 ≤ 2082124152657^3187*1250000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      544027393 1250000000 2082124152657 6250000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2107783733/5000000000 : ℝ)^4211 ≤ (7984731383347/25000000000000 : ℝ)^3187 := by
    have hnat : (2107783733 : ℕ)^4211*25000000000000^3187 ≤ 7984731383347^3187*5000000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2107783733 5000000000 7984731383347 25000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4493187033/10000000000 : ℝ)^4211 ≤ (34747088011007/100000000000000 : ℝ)^3187 := by
    have hnat : (4493187033 : ℕ)^4211*100000000000000^3187 ≤ 34747088011007^3187*10000000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4493187033 10000000000 34747088011007 100000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4211/1024 : ℝ)) 4211 3187 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(544027393/1250000000 : ℝ), (2107783733/5000000000 : ℝ), (4493187033/10000000000 : ℝ)] ![(2082124152657/6250000000000 : ℝ), (7984731383347/25000000000000 : ℝ), (34747088011007/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(544027393/1250000000 : ℝ)|^4211 ≤ (2082124152657/6250000000000 : ℝ)^3187
        have hw : |(544027393/1250000000 : ℝ)|=(544027393/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2107783733/5000000000 : ℝ)|^4211 ≤ (7984731383347/25000000000000 : ℝ)^3187
        have hw : |(2107783733/5000000000 : ℝ)|=(2107783733/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4493187033/10000000000 : ℝ)|^4211 ≤ (34747088011007/100000000000000 : ℝ)^3187
        have hw : |(4493187033/10000000000 : ℝ)|=(4493187033/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1229_s4_4 (p : ℝ) (hpa : (8421/2048 : ℝ) ≤ p) (hpb : p ≤ (4211/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1062694777/5000000000 : ℝ)*x 0 + (526121097/1000000000 : ℝ)*x 1 + (5397645971/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062694777/5000000000 : ℝ)^4211 ≤ (6461167250257/50000000000000 : ℝ)^3187 := by
    have hnat : (1062694777 : ℕ)^4211*50000000000000^3187 ≤ 6461167250257^3187*5000000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062694777 5000000000 6461167250257 50000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (526121097/1000000000 : ℝ)^4211 ≤ (1712099774813/4000000000000 : ℝ)^3187 := by
    have hnat : (526121097 : ℕ)^4211*4000000000000^3187 ≤ 1712099774813^3187*1000000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526121097 1000000000 1712099774813 4000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5397645971/10000000000 : ℝ)^4211 ≤ (44275171117601/100000000000000 : ℝ)^3187 := by
    have hnat : (5397645971 : ℕ)^4211*100000000000000^3187 ≤ 44275171117601^3187*10000000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5397645971 10000000000 44275171117601 100000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4211/1024 : ℝ)) 4211 3187 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1062694777/5000000000 : ℝ), (526121097/1000000000 : ℝ), (5397645971/10000000000 : ℝ)] ![(6461167250257/50000000000000 : ℝ), (1712099774813/4000000000000 : ℝ), (44275171117601/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1062694777/5000000000 : ℝ)|^4211 ≤ (6461167250257/50000000000000 : ℝ)^3187
        have hw : |(-1062694777/5000000000 : ℝ)|=(1062694777/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(526121097/1000000000 : ℝ)|^4211 ≤ (1712099774813/4000000000000 : ℝ)^3187
        have hw : |(526121097/1000000000 : ℝ)|=(526121097/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5397645971/10000000000 : ℝ)|^4211 ≤ (44275171117601/100000000000000 : ℝ)^3187
        have hw : |(5397645971/10000000000 : ℝ)|=(5397645971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1229_s4_5 (p : ℝ) (hpa : (8421/2048 : ℝ) ≤ p) (hpb : p ≤ (4211/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5311067491/10000000000 : ℝ)*x 0 + (-2058233001/10000000000 : ℝ)*x 1 + (5397645973/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5311067491/10000000000 : ℝ)^4211 ≤ (10834809766201/25000000000000 : ℝ)^3187 := by
    have hnat : (5311067491 : ℕ)^4211*25000000000000^3187 ≤ 10834809766201^3187*10000000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5311067491 10000000000 10834809766201 25000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2058233001/10000000000 : ℝ)^4211 ≤ (12385589777643/100000000000000 : ℝ)^3187 := by
    have hnat : (2058233001 : ℕ)^4211*100000000000000^3187 ≤ 12385589777643^3187*10000000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2058233001 10000000000 12385589777643 100000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5397645973/10000000000 : ℝ)^4211 ≤ (22137585569639/50000000000000 : ℝ)^3187 := by
    have hnat : (5397645973 : ℕ)^4211*50000000000000^3187 ≤ 22137585569639^3187*10000000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5397645973 10000000000 22137585569639 50000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4211/1024 : ℝ)) 4211 3187 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5311067491/10000000000 : ℝ), (-2058233001/10000000000 : ℝ), (5397645973/10000000000 : ℝ)] ![(10834809766201/25000000000000 : ℝ), (12385589777643/100000000000000 : ℝ), (22137585569639/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5311067491/10000000000 : ℝ)|^4211 ≤ (10834809766201/25000000000000 : ℝ)^3187
        have hw : |(5311067491/10000000000 : ℝ)|=(5311067491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2058233001/10000000000 : ℝ)|^4211 ≤ (12385589777643/100000000000000 : ℝ)^3187
        have hw : |(-2058233001/10000000000 : ℝ)|=(2058233001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5397645973/10000000000 : ℝ)|^4211 ≤ (22137585569639/50000000000000 : ℝ)^3187
        have hw : |(5397645973/10000000000 : ℝ)|=(5397645973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1229_s4_6 (p : ℝ) (hpa : (8421/2048 : ℝ) ≤ p) (hpb : p ≤ (4211/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5311067227/10000000000 : ℝ)*x 0 + (5397646351/10000000000 : ℝ)*x 1 + (-514558211/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5311067227/10000000000 : ℝ)^4211 ≤ (21669618109167/50000000000000 : ℝ)^3187 := by
    have hnat : (5311067227 : ℕ)^4211*50000000000000^3187 ≤ 21669618109167^3187*10000000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5311067227 10000000000 21669618109167 50000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5397646351/10000000000 : ℝ)^4211 ≤ (8855035047227/20000000000000 : ℝ)^3187 := by
    have hnat : (5397646351 : ℕ)^4211*20000000000000^3187 ≤ 8855035047227^3187*10000000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5397646351 10000000000 8855035047227 20000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (514558211/2500000000 : ℝ)^4211 ≤ (6192794264663/50000000000000 : ℝ)^3187 := by
    have hnat : (514558211 : ℕ)^4211*50000000000000^3187 ≤ 6192794264663^3187*2500000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      514558211 2500000000 6192794264663 50000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4211/1024 : ℝ)) 4211 3187 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5311067227/10000000000 : ℝ), (5397646351/10000000000 : ℝ), (-514558211/2500000000 : ℝ)] ![(21669618109167/50000000000000 : ℝ), (8855035047227/20000000000000 : ℝ), (6192794264663/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5311067227/10000000000 : ℝ)|^4211 ≤ (21669618109167/50000000000000 : ℝ)^3187
        have hw : |(5311067227/10000000000 : ℝ)|=(5311067227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5397646351/10000000000 : ℝ)|^4211 ≤ (8855035047227/20000000000000 : ℝ)^3187
        have hw : |(5397646351/10000000000 : ℝ)|=(5397646351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-514558211/2500000000 : ℝ)|^4211 ≤ (6192794264663/50000000000000 : ℝ)^3187
        have hw : |(-514558211/2500000000 : ℝ)|=(514558211/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1229_s4_7 (p : ℝ) (hpa : (8421/2048 : ℝ) ≤ p) (hpb : p ≤ (4211/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2176115989/5000000000 : ℝ)*x 0 + (2246207903/5000000000 : ℝ)*x 1 + (84326833/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2176115989/5000000000 : ℝ)^4211 ≤ (16657058122239/50000000000000 : ℝ)^3187 := by
    have hnat : (2176115989 : ℕ)^4211*50000000000000^3187 ≤ 16657058122239^3187*5000000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2176115989 5000000000 16657058122239 50000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2246207903/5000000000 : ℝ)^4211 ≤ (4342400976139/12500000000000 : ℝ)^3187 := by
    have hnat : (2246207903 : ℕ)^4211*12500000000000^3187 ≤ 4342400976139^3187*5000000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2246207903 5000000000 4342400976139 12500000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (84326833/200000000 : ℝ)^4211 ≤ (15973337969573/50000000000000 : ℝ)^3187 := by
    have hnat : (84326833 : ℕ)^4211*50000000000000^3187 ≤ 15973337969573^3187*200000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84326833 200000000 15973337969573 50000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4211/1024 : ℝ)) 4211 3187 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2176115989/5000000000 : ℝ), (2246207903/5000000000 : ℝ), (84326833/200000000 : ℝ)] ![(16657058122239/50000000000000 : ℝ), (4342400976139/12500000000000 : ℝ), (15973337969573/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2176115989/5000000000 : ℝ)|^4211 ≤ (16657058122239/50000000000000 : ℝ)^3187
        have hw : |(2176115989/5000000000 : ℝ)|=(2176115989/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2246207903/5000000000 : ℝ)|^4211 ≤ (4342400976139/12500000000000 : ℝ)^3187
        have hw : |(2246207903/5000000000 : ℝ)|=(2246207903/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(84326833/200000000 : ℝ)|^4211 ≤ (15973337969573/50000000000000 : ℝ)^3187
        have hw : |(84326833/200000000 : ℝ)|=(84326833/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1229_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8421/2048 : ℝ) ≤ p) (hpb : p ≤ (4211/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151173987/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14713/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10877/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1133/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3559/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14713/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10877/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14713/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10877/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14713/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10877/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14713/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10877/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14713/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10877/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14713/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10877/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10877/100000 : ℝ) ^ (8421/2048 : ℝ) ≤ (2730501604679971/25000000000000000000 : ℝ) := by
    have hpowers : (10877/100000 : ℝ)^8421 ≤ (2730501604679971/25000000000000000000 : ℝ)^2048 := by
      have hnat : (10877 : ℕ)^8421*25000000000000000000^2048 ≤ 2730501604679971^2048*100000^8421 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10877 100000 2730501604679971 25000000000000000000 8421 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10877/100000 : ℝ)) (X := (2730501604679971/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8421 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14713/100000 : ℝ) ^ (8421/2048 : ℝ) ≤ (37821633600033191/100000000000000000000 : ℝ) := by
    have hpowers : (14713/100000 : ℝ)^8421 ≤ (37821633600033191/100000000000000000000 : ℝ)^2048 := by
      have hnat : (14713 : ℕ)^8421*100000000000000000000^2048 ≤ 37821633600033191^2048*100000^8421 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14713 100000 37821633600033191 100000000000000000000 8421 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14713/100000 : ℝ)) (X := (37821633600033191/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8421 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (12502730501604679971/12500000000000000000 : ℝ) ≤ (10000531205806319/10000000000000000 : ℝ) ^ (8421/2048 : ℝ) := by
    have hpowers : (12502730501604679971/12500000000000000000 : ℝ)^2048 ≤ (10000531205806319/10000000000000000 : ℝ)^8421 := by
      have hnat : (12502730501604679971 : ℕ)^2048*10000000000000000^8421 ≤ 10000531205806319^8421*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12502730501604679971 12500000000000000000 10000531205806319 10000000000000000 2048 8421 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000531205806319/10000000000000000 : ℝ)) (X := (12502730501604679971/12500000000000000000 : ℝ)) (by norm_num) 8421 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (4001949745600750123/4000000000000000000 : ℝ) ≤ (1000118523414523/1000000000000000 : ℝ) ^ (8421/2048 : ℝ) := by
    have hpowers : (4001949745600750123/4000000000000000000 : ℝ)^2048 ≤ (1000118523414523/1000000000000000 : ℝ)^8421 := by
      have hnat : (4001949745600750123 : ℕ)^2048*1000000000000000^8421 ≤ 1000118523414523^8421*4000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4001949745600750123 4000000000000000000 1000118523414523 1000000000000000 2048 8421 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000118523414523/1000000000000000 : ℝ)) (X := (4001949745600750123/4000000000000000000 : ℝ)) (by norm_num) 8421 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50037821633600033191/50000000000000000000 : ℝ) ≤ (10001839262484141/10000000000000000 : ℝ) ^ (8421/2048 : ℝ) := by
    have hpowers : (50037821633600033191/50000000000000000000 : ℝ)^2048 ≤ (10001839262484141/10000000000000000 : ℝ)^8421 := by
      have hnat : (50037821633600033191 : ℕ)^2048*10000000000000000^8421 ≤ 10001839262484141^8421*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50037821633600033191 50000000000000000000 10001839262484141 10000000000000000 2048 8421 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001839262484141/10000000000000000 : ℝ)) (X := (50037821633600033191/50000000000000000000 : ℝ)) (by norm_num) 8421 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2730501604679971/25000000000000000000 : ℝ) ≤ ((3834780997298836979/3836000000000000000 : ℝ)+2*(654028338911/383600000000000 : ℝ)*(10877/100000 : ℝ))^(8421/2048 : ℝ) := by
    rw [show (3834780997298836979/3836000000000000000 : ℝ)+2*(654028338911/383600000000000 : ℝ)*(10877/100000 : ℝ)=(10000531205806319/10000000000000000 : ℝ) by norm_num, show 1+2*(2730501604679971/25000000000000000000 : ℝ)=(12502730501604679971/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(37821633600033191/100000000000000000000 : ℝ)+(2730501604679971/25000000000000000000 : ℝ) ≤ ((3834780997298836979/3836000000000000000 : ℝ)+(654028338911/383600000000000 : ℝ)*((14713/100000 : ℝ)+(10877/100000 : ℝ)))^(8421/2048 : ℝ) := by
    rw [show (3834780997298836979/3836000000000000000 : ℝ)+(654028338911/383600000000000 : ℝ)*((14713/100000 : ℝ)+(10877/100000 : ℝ))=(1000118523414523/1000000000000000 : ℝ) by norm_num, show 1+(37821633600033191/100000000000000000000 : ℝ)+(2730501604679971/25000000000000000000 : ℝ)=(4001949745600750123/4000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(37821633600033191/100000000000000000000 : ℝ) ≤ ((3834780997298836979/3836000000000000000 : ℝ)+2*(654028338911/383600000000000 : ℝ)*(14713/100000 : ℝ))^(8421/2048 : ℝ) := by
    rw [show (3834780997298836979/3836000000000000000 : ℝ)+2*(654028338911/383600000000000 : ℝ)*(14713/100000 : ℝ)=(10001839262484141/10000000000000000 : ℝ) by norm_num, show 1+2*(37821633600033191/100000000000000000000 : ℝ)=(50037821633600033191/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3834780997298836979/3836000000000000000 : ℝ)*(X 1 0+X 2 0)+(654028338911/383600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8421/2048 : ℝ)) (lo := (10877/100000 : ℝ)) (hi := (14713/100000 : ℝ)) (c := (3834780997298836979/3836000000000000000 : ℝ)) (alpha := (654028338911/383600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3834780997298836979/3836000000000000000 : ℝ)*(X 0 1+X 2 1)+(654028338911/383600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8421/2048 : ℝ)) (lo := (10877/100000 : ℝ)) (hi := (14713/100000 : ℝ)) (c := (3834780997298836979/3836000000000000000 : ℝ)) (alpha := (654028338911/383600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3834780997298836979/3836000000000000000 : ℝ)*(X 0 2+X 1 2)+(654028338911/383600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8421/2048 : ℝ)) (lo := (10877/100000 : ℝ)) (hi := (14713/100000 : ℝ)) (c := (3834780997298836979/3836000000000000000 : ℝ)) (alpha := (654028338911/383600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2125383029/10000000000 : ℝ)*X 0 0+(1349507217/2500000000 : ℝ)*X 0 1+(2630414889/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1229_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5346041713/10000000000 : ℝ)*X 1 0+(-548762283/2500000000 : ℝ)*X 1 1+(5260829781/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1229_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((534604173/1000000000 : ℝ)*X 2 0+(5260829793/10000000000 : ℝ)*X 2 1+(-439009819/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1229_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((544027393/1250000000 : ℝ)*X 0 0+(2107783733/5000000000 : ℝ)*X 0 1+(4493187033/10000000000 : ℝ)*X 0 2+(544027393/1250000000 : ℝ)*X 1 0+(2107783733/5000000000 : ℝ)*X 1 1+(4493187033/10000000000 : ℝ)*X 1 2+(544027393/1250000000 : ℝ)*X 2 0+(2107783733/5000000000 : ℝ)*X 2 1+(4493187033/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1229_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1062694777/5000000000 : ℝ)*X 0 0+(526121097/1000000000 : ℝ)*X 0 1+(5397645971/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1229_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5311067491/10000000000 : ℝ)*X 1 0+(-2058233001/10000000000 : ℝ)*X 1 1+(5397645973/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1229_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5311067227/10000000000 : ℝ)*X 2 0+(5397646351/10000000000 : ℝ)*X 2 1+(-514558211/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1229_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2176115989/5000000000 : ℝ)*X 0 0+(2246207903/5000000000 : ℝ)*X 0 1+(84326833/200000000 : ℝ)*X 0 2+(2176115989/5000000000 : ℝ)*X 1 0+(2246207903/5000000000 : ℝ)*X 1 1+(84326833/200000000 : ℝ)*X 1 2+(2176115989/5000000000 : ℝ)*X 2 0+(2246207903/5000000000 : ℝ)*X 2 1+(84326833/200000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1229_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (203457100487245081007395419/23975000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (20266487/1250000000000 : ℝ)*(base19) + (1480164211/100000000000000 : ℝ)*(base23) + (21963203/25000000000000 : ℝ)*(lower2) + (190249327/100000000000000 : ℝ)*(upper3) + (32141131/25000000000000 : ℝ)*(upper5) + (680678544619929/12500000000000 : ℝ)*(major0) + (680678544619929/12500000000000 : ℝ)*(major1) + (680678544619929/12500000000000 : ℝ)*(major2) + (7288720517519619/100000000000000 : ℝ)*(sp0) + (364438065567607/5000000000000 : ℝ)*(sp1) + (911095181563361/12500000000000 : ℝ)*(sp2) + (3602071439242293/100000000000000 : ℝ)*(sp3) + (42415151481/100000000000000 : ℝ)*(sp4) + (22059131493/100000000000000 : ℝ)*(sp7) + (1801046749186893/50000000000000 : ℝ)*(f.failure) + (7288762932671099/100000000000000 : ℝ)*(f.sum) + (25560983718443/4795000000000000000000000000 : ℝ)*base65 + (170609386891050787/6850000000000000000000000000000 : ℝ)*base68 + (130541627049950787/6850000000000000000000000000000 : ℝ)*base70 + (49022780185850787/6850000000000000000000000000000 : ℝ)*base72 + (7468578552541/2397500000000000000000000000 : ℝ)*base74 + (119453762942900787/6850000000000000000000000000000 : ℝ)*base76 + (18119830062850787/6850000000000000000000000000000 : ℝ)*base78 + (114170910196750787/6850000000000000000000000000000 : ℝ)*base80 + (14148036009767/4795000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (22952391/5000000000000000000000 : ℝ)*base89 + (22952391/5000000000000000000000 : ℝ)*base91 + (22952391/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (286831531925518680365387679/47950000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (116456707/10000000000000 : ℝ)*(base19) + (1034994231/100000000000000 : ℝ)*(base23) + (3966823/6250000000000 : ℝ)*(upper2) + (164948763/50000000000000 : ℝ)*(upper3) + (58002879/50000000000000 : ℝ)*(upper5) + (1368962638437411/25000000000000 : ℝ)*(major0) + (1368962638437411/25000000000000 : ℝ)*(major1) + (1368962638437411/25000000000000 : ℝ)*(major2) + (15169503157/100000000000000 : ℝ)*(sp1) + (32671319179/100000000000000 : ℝ)*(sp2) + (916185430875823/12500000000000 : ℝ)*(sp4) + (1832366778234089/25000000000000 : ℝ)*(sp5) + (3664724870346587/50000000000000 : ℝ)*(sp6) + (905554365274107/25000000000000 : ℝ)*(sp7) + (905554365274107/25000000000000 : ℝ)*(f.failure) + (916185430875823/12500000000000 : ℝ)*(f.sum) + (19224686124261/4795000000000000000000000000 : ℝ)*base65 + (28153529702118767/13700000000000000000000000000000 : ℝ)*base67 + (128476823822918767/13700000000000000000000000000000 : ℝ)*base69 + (112603098842018767/13700000000000000000000000000000 : ℝ)*base71 + (4659188928539/4795000000000000000000000000 : ℝ)*base74 + (274385386631218767/13700000000000000000000000000000 : ℝ)*base75 + (97991262037318767/13700000000000000000000000000000 : ℝ)*base77 + (70018242590418767/13700000000000000000000000000000 : ℝ)*base79 + (10813377150979/1198750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (3054609/2500000000000000000000 : ℝ)*base89 + (3054609/2500000000000000000000 : ℝ)*base91 + (3054609/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1229_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8421/2048 : ℝ) ≤ p) (hpb : p ≤ (4211/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151173987/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14713/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10877/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1133/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3559/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1229_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1229_s5_0 (p : ℝ) (hpa : (8421/2048 : ℝ) ≤ p) (hpb : p ≤ (4211/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1062926717/5000000000 : ℝ)*x 0 + (168522663/312500000 : ℝ)*x 1 + (1053164861/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062926717/5000000000 : ℝ)^4211 ≤ (2585212243633/20000000000000 : ℝ)^3187 := by
    have hnat : (1062926717 : ℕ)^4211*20000000000000^3187 ≤ 2585212243633^3187*5000000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062926717 5000000000 2585212243633 20000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (168522663/312500000 : ℝ)^4211 ≤ (1381932705431/3125000000000 : ℝ)^3187 := by
    have hnat : (168522663 : ℕ)^4211*3125000000000^3187 ≤ 1381932705431^3187*312500000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      168522663 312500000 1381932705431 3125000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1053164861/2000000000 : ℝ)^4211 ≤ (10713023050619/25000000000000 : ℝ)^3187 := by
    have hnat : (1053164861 : ℕ)^4211*25000000000000^3187 ≤ 10713023050619^3187*2000000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053164861 2000000000 10713023050619 25000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4211/1024 : ℝ)) 4211 3187 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1062926717/5000000000 : ℝ), (168522663/312500000 : ℝ), (1053164861/2000000000 : ℝ)] ![(2585212243633/20000000000000 : ℝ), (1381932705431/3125000000000 : ℝ), (10713023050619/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1062926717/5000000000 : ℝ)|^4211 ≤ (2585212243633/20000000000000 : ℝ)^3187
        have hw : |(-1062926717/5000000000 : ℝ)|=(1062926717/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(168522663/312500000 : ℝ)|^4211 ≤ (1381932705431/3125000000000 : ℝ)^3187
        have hw : |(168522663/312500000 : ℝ)|=(168522663/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1053164861/2000000000 : ℝ)|^4211 ≤ (10713023050619/25000000000000 : ℝ)^3187
        have hw : |(1053164861/2000000000 : ℝ)|=(1053164861/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1229_s5_1 (p : ℝ) (hpa : (8421/2048 : ℝ) ≤ p) (hpb : p ≤ (4211/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (668087677/1250000000 : ℝ)*x 0 + (-2190216381/10000000000 : ℝ)*x 1 + (5265824327/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668087677/1250000000 : ℝ)^4211 ≤ (10925562807353/25000000000000 : ℝ)^3187 := by
    have hnat : (668087677 : ℕ)^4211*25000000000000^3187 ≤ 10925562807353^3187*1250000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668087677 1250000000 10925562807353 25000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2190216381/10000000000 : ℝ)^4211 ≤ (6722828156331/50000000000000 : ℝ)^3187 := by
    have hnat : (2190216381 : ℕ)^4211*50000000000000^3187 ≤ 6722828156331^3187*10000000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2190216381 10000000000 6722828156331 50000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265824327/10000000000 : ℝ)^4211 ≤ (4285209243903/10000000000000 : ℝ)^3187 := by
    have hnat : (5265824327 : ℕ)^4211*10000000000000^3187 ≤ 4285209243903^3187*10000000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265824327 10000000000 4285209243903 10000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4211/1024 : ℝ)) 4211 3187 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668087677/1250000000 : ℝ), (-2190216381/10000000000 : ℝ), (5265824327/10000000000 : ℝ)] ![(10925562807353/25000000000000 : ℝ), (6722828156331/50000000000000 : ℝ), (4285209243903/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668087677/1250000000 : ℝ)|^4211 ≤ (10925562807353/25000000000000 : ℝ)^3187
        have hw : |(668087677/1250000000 : ℝ)|=(668087677/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2190216381/10000000000 : ℝ)|^4211 ≤ (6722828156331/50000000000000 : ℝ)^3187
        have hw : |(-2190216381/10000000000 : ℝ)|=(2190216381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265824327/10000000000 : ℝ)|^4211 ≤ (4285209243903/10000000000000 : ℝ)^3187
        have hw : |(5265824327/10000000000 : ℝ)|=(5265824327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1229_s5_2 (p : ℝ) (hpa : (8421/2048 : ℝ) ≤ p) (hpb : p ≤ (4211/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2672350789/5000000000 : ℝ)*x 0 + (5265824447/10000000000 : ℝ)*x 1 + (-2190216007/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672350789/5000000000 : ℝ)^4211 ≤ (5462781622457/12500000000000 : ℝ)^3187 := by
    have hnat : (2672350789 : ℕ)^4211*12500000000000^3187 ≤ 5462781622457^3187*5000000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672350789 5000000000 5462781622457 12500000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265824447/10000000000 : ℝ)^4211 ≤ (2678255858083/6250000000000 : ℝ)^3187 := by
    have hnat : (5265824447 : ℕ)^4211*6250000000000^3187 ≤ 2678255858083^3187*10000000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265824447 10000000000 2678255858083 6250000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2190216007/10000000000 : ℝ)^4211 ≤ (6722826639491/50000000000000 : ℝ)^3187 := by
    have hnat : (2190216007 : ℕ)^4211*50000000000000^3187 ≤ 6722826639491^3187*10000000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2190216007 10000000000 6722826639491 50000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4211/1024 : ℝ)) 4211 3187 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672350789/5000000000 : ℝ), (5265824447/10000000000 : ℝ), (-2190216007/10000000000 : ℝ)] ![(5462781622457/12500000000000 : ℝ), (2678255858083/6250000000000 : ℝ), (6722826639491/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672350789/5000000000 : ℝ)|^4211 ≤ (5462781622457/12500000000000 : ℝ)^3187
        have hw : |(2672350789/5000000000 : ℝ)|=(2672350789/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265824447/10000000000 : ℝ)|^4211 ≤ (2678255858083/6250000000000 : ℝ)^3187
        have hw : |(5265824447/10000000000 : ℝ)|=(5265824447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2190216007/10000000000 : ℝ)|^4211 ≤ (6722826639491/50000000000000 : ℝ)^3187
        have hw : |(-2190216007/10000000000 : ℝ)|=(2190216007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1229_s5_3 (p : ℝ) (hpa : (8421/2048 : ℝ) ≤ p) (hpb : p ≤ (4211/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (272030937/625000000 : ℝ)*x 0 + (528244027/1250000000 : ℝ)*x 1 + (89654639/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (272030937/625000000 : ℝ)^4211 ≤ (33316776372399/100000000000000 : ℝ)^3187 := by
    have hnat : (272030937 : ℕ)^4211*100000000000000^3187 ≤ 33316776372399^3187*625000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      272030937 625000000 33316776372399 100000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (528244027/1250000000 : ℝ)^4211 ≤ (6408585197071/20000000000000 : ℝ)^3187 := by
    have hnat : (528244027 : ℕ)^4211*20000000000000^3187 ≤ 6408585197071^3187*1250000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528244027 1250000000 6408585197071 20000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (89654639/200000000 : ℝ)^4211 ≤ (34640297634671/100000000000000 : ℝ)^3187 := by
    have hnat : (89654639 : ℕ)^4211*100000000000000^3187 ≤ 34640297634671^3187*200000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      89654639 200000000 34640297634671 100000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4211/1024 : ℝ)) 4211 3187 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(272030937/625000000 : ℝ), (528244027/1250000000 : ℝ), (89654639/200000000 : ℝ)] ![(33316776372399/100000000000000 : ℝ), (6408585197071/20000000000000 : ℝ), (34640297634671/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(272030937/625000000 : ℝ)|^4211 ≤ (33316776372399/100000000000000 : ℝ)^3187
        have hw : |(272030937/625000000 : ℝ)|=(272030937/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(528244027/1250000000 : ℝ)|^4211 ≤ (6408585197071/20000000000000 : ℝ)^3187
        have hw : |(528244027/1250000000 : ℝ)|=(528244027/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(89654639/200000000 : ℝ)|^4211 ≤ (34640297634671/100000000000000 : ℝ)^3187
        have hw : |(89654639/200000000 : ℝ)|=(89654639/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1229_s5_4 (p : ℝ) (hpa : (8421/2048 : ℝ) ≤ p) (hpb : p ≤ (4211/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2125858321/10000000000 : ℝ)*x 0 + (5266150817/10000000000 : ℝ)*x 1 + (2696198781/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2125858321/10000000000 : ℝ)^4211 ≤ (12926100480721/100000000000000 : ℝ)^3187 := by
    have hnat : (2125858321 : ℕ)^4211*100000000000000^3187 ≤ 12926100480721^3187*10000000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2125858321 10000000000 12926100480721 100000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266150817/10000000000 : ℝ)^4211 ≤ (21427801526409/50000000000000 : ℝ)^3187 := by
    have hnat : (5266150817 : ℕ)^4211*50000000000000^3187 ≤ 21427801526409^3187*10000000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266150817 10000000000 21427801526409 50000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2696198781/5000000000 : ℝ)^4211 ≤ (22109148227053/50000000000000 : ℝ)^3187 := by
    have hnat : (2696198781 : ℕ)^4211*50000000000000^3187 ≤ 22109148227053^3187*5000000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696198781 5000000000 22109148227053 50000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4211/1024 : ℝ)) 4211 3187 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2125858321/10000000000 : ℝ), (5266150817/10000000000 : ℝ), (2696198781/5000000000 : ℝ)] ![(12926100480721/100000000000000 : ℝ), (21427801526409/50000000000000 : ℝ), (22109148227053/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2125858321/10000000000 : ℝ)|^4211 ≤ (12926100480721/100000000000000 : ℝ)^3187
        have hw : |(-2125858321/10000000000 : ℝ)|=(2125858321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266150817/10000000000 : ℝ)|^4211 ≤ (21427801526409/50000000000000 : ℝ)^3187
        have hw : |(5266150817/10000000000 : ℝ)|=(5266150817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2696198781/5000000000 : ℝ)|^4211 ≤ (22109148227053/50000000000000 : ℝ)^3187
        have hw : |(2696198781/5000000000 : ℝ)|=(2696198781/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1229_s5_5 (p : ℝ) (hpa : (8421/2048 : ℝ) ≤ p) (hpb : p ≤ (4211/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5312351073/10000000000 : ℝ)*x 0 + (-2063643123/10000000000 : ℝ)*x 1 + (5392397569/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312351073/10000000000 : ℝ)^4211 ≤ (4335307928879/10000000000000 : ℝ)^3187 := by
    have hnat : (5312351073 : ℕ)^4211*10000000000000^3187 ≤ 4335307928879^3187*10000000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312351073 10000000000 4335307928879 10000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2063643123/10000000000 : ℝ)^4211 ≤ (12428624166251/100000000000000 : ℝ)^3187 := by
    have hnat : (2063643123 : ℕ)^4211*100000000000000^3187 ≤ 12428624166251^3187*10000000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2063643123 10000000000 12428624166251 100000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392397569/10000000000 : ℝ)^4211 ≤ (884365930599/2000000000000 : ℝ)^3187 := by
    have hnat : (5392397569 : ℕ)^4211*2000000000000^3187 ≤ 884365930599^3187*10000000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392397569 10000000000 884365930599 2000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4211/1024 : ℝ)) 4211 3187 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312351073/10000000000 : ℝ), (-2063643123/10000000000 : ℝ), (5392397569/10000000000 : ℝ)] ![(4335307928879/10000000000000 : ℝ), (12428624166251/100000000000000 : ℝ), (884365930599/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312351073/10000000000 : ℝ)|^4211 ≤ (4335307928879/10000000000000 : ℝ)^3187
        have hw : |(5312351073/10000000000 : ℝ)|=(5312351073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2063643123/10000000000 : ℝ)|^4211 ≤ (12428624166251/100000000000000 : ℝ)^3187
        have hw : |(-2063643123/10000000000 : ℝ)|=(2063643123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392397569/10000000000 : ℝ)|^4211 ≤ (884365930599/2000000000000 : ℝ)^3187
        have hw : |(5392397569/10000000000 : ℝ)|=(5392397569/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1229_s5_6 (p : ℝ) (hpa : (8421/2048 : ℝ) ≤ p) (hpb : p ≤ (4211/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (531235107/1000000000 : ℝ)*x 0 + (21064053/39062500 : ℝ)*x 1 + (-2063643129/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (531235107/1000000000 : ℝ)^4211 ≤ (21676539628221/50000000000000 : ℝ)^3187 := by
    have hnat : (531235107 : ℕ)^4211*50000000000000^3187 ≤ 21676539628221^3187*1000000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      531235107 1000000000 21676539628221 50000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (21064053/39062500 : ℝ)^4211 ≤ (8843659303823/20000000000000 : ℝ)^3187 := by
    have hnat : (21064053 : ℕ)^4211*20000000000000^3187 ≤ 8843659303823^3187*39062500^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21064053 39062500 8843659303823 20000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2063643129/10000000000 : ℝ)^4211 ≤ (6214312106999/50000000000000 : ℝ)^3187 := by
    have hnat : (2063643129 : ℕ)^4211*50000000000000^3187 ≤ 6214312106999^3187*10000000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2063643129 10000000000 6214312106999 50000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4211/1024 : ℝ)) 4211 3187 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(531235107/1000000000 : ℝ), (21064053/39062500 : ℝ), (-2063643129/10000000000 : ℝ)] ![(21676539628221/50000000000000 : ℝ), (8843659303823/20000000000000 : ℝ), (6214312106999/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(531235107/1000000000 : ℝ)|^4211 ≤ (21676539628221/50000000000000 : ℝ)^3187
        have hw : |(531235107/1000000000 : ℝ)|=(531235107/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(21064053/39062500 : ℝ)|^4211 ≤ (8843659303823/20000000000000 : ℝ)^3187
        have hw : |(21064053/39062500 : ℝ)|=(21064053/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2063643129/10000000000 : ℝ)|^4211 ≤ (6214312106999/50000000000000 : ℝ)^3187
        have hw : |(-2063643129/10000000000 : ℝ)|=(2063643129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1229_s5_7 (p : ℝ) (hpa : (8421/2048 : ℝ) ≤ p) (hpb : p ≤ (4211/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4352505433/10000000000 : ℝ)*x 0 + (560258997/1250000000 : ℝ)*x 1 + (1056653561/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4352505433/10000000000 : ℝ)^4211 ≤ (33316881973911/100000000000000 : ℝ)^3187 := by
    have hnat : (4352505433 : ℕ)^4211*100000000000000^3187 ≤ 33316881973911^3187*10000000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4352505433 10000000000 33316881973911 100000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (560258997/1250000000 : ℝ)^4211 ≤ (34633559206917/100000000000000 : ℝ)^3187 := by
    have hnat : (560258997 : ℕ)^4211*100000000000000^3187 ≤ 34633559206917^3187*1250000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      560258997 1250000000 34633559206917 100000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1056653561/2500000000 : ℝ)^4211 ≤ (32049558802887/100000000000000 : ℝ)^3187 := by
    have hnat : (1056653561 : ℕ)^4211*100000000000000^3187 ≤ 32049558802887^3187*2500000000^4211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056653561 2500000000 32049558802887 100000000000000 4211 3187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4211/1024 : ℝ)) 4211 3187 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4352505433/10000000000 : ℝ), (560258997/1250000000 : ℝ), (1056653561/2500000000 : ℝ)] ![(33316881973911/100000000000000 : ℝ), (34633559206917/100000000000000 : ℝ), (32049558802887/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4352505433/10000000000 : ℝ)|^4211 ≤ (33316881973911/100000000000000 : ℝ)^3187
        have hw : |(4352505433/10000000000 : ℝ)|=(4352505433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(560258997/1250000000 : ℝ)|^4211 ≤ (34633559206917/100000000000000 : ℝ)^3187
        have hw : |(560258997/1250000000 : ℝ)|=(560258997/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1056653561/2500000000 : ℝ)|^4211 ≤ (32049558802887/100000000000000 : ℝ)^3187
        have hw : |(1056653561/2500000000 : ℝ)|=(1056653561/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1229_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8421/2048 : ℝ) ≤ p) (hpb : p ≤ (4211/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151173987/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3559/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1133/10000 : ℝ)*pair X i i ≤ pair X i h) :
    (11437/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (113/800 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3559/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1133/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3559/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1133/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3559/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1133/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3559/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1133/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3559/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1133/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3559/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1133/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1133/10000 : ℝ) ^ (8421/2048 : ℝ) ≤ (2583431927323649/20000000000000000000 : ℝ) := by
    have hpowers : (1133/10000 : ℝ)^8421 ≤ (2583431927323649/20000000000000000000 : ℝ)^2048 := by
      have hnat : (1133 : ℕ)^8421*20000000000000000000^2048 ≤ 2583431927323649^2048*10000^8421 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1133 10000 2583431927323649 20000000000000000000 8421 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1133/10000 : ℝ)) (X := (2583431927323649/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8421 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (3559/25000 : ℝ) ^ (8421/2048 : ℝ) ≤ (33028344337267601/100000000000000000000 : ℝ) := by
    have hpowers : (3559/25000 : ℝ)^8421 ≤ (33028344337267601/100000000000000000000 : ℝ)^2048 := by
      have hnat : (3559 : ℕ)^8421*100000000000000000000^2048 ≤ 33028344337267601^2048*25000^8421 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3559 25000 33028344337267601 100000000000000000000 8421 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3559/25000 : ℝ)) (X := (33028344337267601/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8421 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (10002583431927323649/10000000000000000000 : ℝ) ≤ (2500157058290187/2500000000000000 : ℝ) ^ (8421/2048 : ℝ) := by
    have hpowers : (10002583431927323649/10000000000000000000 : ℝ)^2048 ≤ (2500157058290187/2500000000000000 : ℝ)^8421 := by
      have hnat : (10002583431927323649 : ℕ)^2048*2500000000000000^8421 ≤ 2500157058290187^8421*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002583431927323649 10000000000000000000 2500157058290187 2500000000000000 2048 8421 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500157058290187/2500000000000000 : ℝ)) (X := (10002583431927323649/10000000000000000000 : ℝ)) (by norm_num) 8421 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50022972751986942923/50000000000000000000 : ℝ) ≤ (1250139650928009/1250000000000000 : ℝ) ^ (8421/2048 : ℝ) := by
    have hpowers : (50022972751986942923/50000000000000000000 : ℝ)^2048 ≤ (1250139650928009/1250000000000000 : ℝ)^8421 := by
      have hnat : (50022972751986942923 : ℕ)^2048*1250000000000000^8421 ≤ 1250139650928009^8421*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50022972751986942923 50000000000000000000 1250139650928009 1250000000000000 2048 8421 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250139650928009/1250000000000000 : ℝ)) (X := (50022972751986942923/50000000000000000000 : ℝ)) (by norm_num) 8421 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50033028344337267601/50000000000000000000 : ℝ) ≤ (2500401545421849/2500000000000000 : ℝ) ^ (8421/2048 : ℝ) := by
    have hpowers : (50033028344337267601/50000000000000000000 : ℝ)^2048 ≤ (2500401545421849/2500000000000000 : ℝ)^8421 := by
      have hnat : (50033028344337267601 : ℕ)^2048*2500000000000000^8421 ≤ 2500401545421849^8421*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50033028344337267601 50000000000000000000 2500401545421849 2500000000000000 2048 8421 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500401545421849/2500000000000000 : ℝ)) (X := (50033028344337267601/50000000000000000000 : ℝ)) (by norm_num) 8421 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2583431927323649/20000000000000000000 : ℝ) ≤ ((3631343186094776481/3632500000000000000 : ℝ)+2*(122243565831/72650000000000 : ℝ)*(1133/10000 : ℝ))^(8421/2048 : ℝ) := by
    rw [show (3631343186094776481/3632500000000000000 : ℝ)+2*(122243565831/72650000000000 : ℝ)*(1133/10000 : ℝ)=(2500157058290187/2500000000000000 : ℝ) by norm_num, show 1+2*(2583431927323649/20000000000000000000 : ℝ)=(10002583431927323649/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(33028344337267601/100000000000000000000 : ℝ)+(2583431927323649/20000000000000000000 : ℝ) ≤ ((3631343186094776481/3632500000000000000 : ℝ)+(122243565831/72650000000000 : ℝ)*((3559/25000 : ℝ)+(1133/10000 : ℝ)))^(8421/2048 : ℝ) := by
    rw [show (3631343186094776481/3632500000000000000 : ℝ)+(122243565831/72650000000000 : ℝ)*((3559/25000 : ℝ)+(1133/10000 : ℝ))=(1250139650928009/1250000000000000 : ℝ) by norm_num, show 1+(33028344337267601/100000000000000000000 : ℝ)+(2583431927323649/20000000000000000000 : ℝ)=(50022972751986942923/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(33028344337267601/100000000000000000000 : ℝ) ≤ ((3631343186094776481/3632500000000000000 : ℝ)+2*(122243565831/72650000000000 : ℝ)*(3559/25000 : ℝ))^(8421/2048 : ℝ) := by
    rw [show (3631343186094776481/3632500000000000000 : ℝ)+2*(122243565831/72650000000000 : ℝ)*(3559/25000 : ℝ)=(2500401545421849/2500000000000000 : ℝ) by norm_num, show 1+2*(33028344337267601/100000000000000000000 : ℝ)=(50033028344337267601/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3631343186094776481/3632500000000000000 : ℝ)*(X 1 0+X 2 0)+(122243565831/72650000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8421/2048 : ℝ)) (lo := (1133/10000 : ℝ)) (hi := (3559/25000 : ℝ)) (c := (3631343186094776481/3632500000000000000 : ℝ)) (alpha := (122243565831/72650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3631343186094776481/3632500000000000000 : ℝ)*(X 0 1+X 2 1)+(122243565831/72650000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8421/2048 : ℝ)) (lo := (1133/10000 : ℝ)) (hi := (3559/25000 : ℝ)) (c := (3631343186094776481/3632500000000000000 : ℝ)) (alpha := (122243565831/72650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3631343186094776481/3632500000000000000 : ℝ)*(X 0 2+X 1 2)+(122243565831/72650000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8421/2048 : ℝ)) (lo := (1133/10000 : ℝ)) (hi := (3559/25000 : ℝ)) (c := (3631343186094776481/3632500000000000000 : ℝ)) (alpha := (122243565831/72650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1062926717/5000000000 : ℝ)*X 0 0+(168522663/312500000 : ℝ)*X 0 1+(1053164861/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1229_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((668087677/1250000000 : ℝ)*X 1 0+(-2190216381/10000000000 : ℝ)*X 1 1+(5265824327/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1229_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672350789/5000000000 : ℝ)*X 2 0+(5265824447/10000000000 : ℝ)*X 2 1+(-2190216007/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1229_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((272030937/625000000 : ℝ)*X 0 0+(528244027/1250000000 : ℝ)*X 0 1+(89654639/200000000 : ℝ)*X 0 2+(272030937/625000000 : ℝ)*X 1 0+(528244027/1250000000 : ℝ)*X 1 1+(89654639/200000000 : ℝ)*X 1 2+(272030937/625000000 : ℝ)*X 2 0+(528244027/1250000000 : ℝ)*X 2 1+(89654639/200000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1229_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2125858321/10000000000 : ℝ)*X 0 0+(5266150817/10000000000 : ℝ)*X 0 1+(2696198781/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1229_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312351073/10000000000 : ℝ)*X 1 0+(-2063643123/10000000000 : ℝ)*X 1 1+(5392397569/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1229_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((531235107/1000000000 : ℝ)*X 2 0+(21064053/39062500 : ℝ)*X 2 1+(-2063643129/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1229_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4352505433/10000000000 : ℝ)*X 0 0+(560258997/1250000000 : ℝ)*X 0 1+(1056653561/2500000000 : ℝ)*X 0 2+(4352505433/10000000000 : ℝ)*X 1 0+(560258997/1250000000 : ℝ)*X 1 1+(1056653561/2500000000 : ℝ)*X 1 2+(4352505433/10000000000 : ℝ)*X 2 0+(560258997/1250000000 : ℝ)*X 2 1+(1056653561/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1229_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (451981987969425094579672617/181625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (367866813/50000000000000 : ℝ)*(base19) + (348774897/50000000000000 : ℝ)*(base23) + (48715963/25000000000000 : ℝ)*(upper4) + (14224923/50000000000000 : ℝ)*(upper5) + (5887320122967473/100000000000000 : ℝ)*(major0) + (5887320122967473/100000000000000 : ℝ)*(major1) + (5887320122967473/100000000000000 : ℝ)*(major2) + (7880196562681671/100000000000000 : ℝ)*(sp0) + (7880224715019499/100000000000000 : ℝ)*(sp1) + (492514951158729/6250000000000 : ℝ)*(sp2) + (3894392813540057/100000000000000 : ℝ)*(sp3) + (43353407787/100000000000000 : ℝ)*(sp4) + (7232668167/50000000000000 : ℝ)*(sp5) + (7433353923/100000000000000 : ℝ)*(sp7) + (194720012344699/5000000000000 : ℝ)*(f.failure) + (3940119958044729/50000000000000 : ℝ)*(f.sum) + (3144576060049/1816250000000000000000000000 : ℝ)*base65 + (2771824623622197487/363250000000000000000000000000000 : ℝ)*base68 + (1955465014099197487/363250000000000000000000000000000 : ℝ)*base70 + (1855762282017697487/363250000000000000000000000000000 : ℝ)*base72 + (21985874782009/7265000000000000000000000000 : ℝ)*base74 + (4934876120926697487/363250000000000000000000000000000 : ℝ)*base76 + (2230887951062197487/363250000000000000000000000000000 : ℝ)*base78 + (6151298438254447487/363250000000000000000000000000000 : ℝ)*base80 + (7022236306771/1816250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1144913/500000000000000000000 : ℝ)*base89 + (1144913/500000000000000000000 : ℝ)*base91 + (1144913/500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1440136068425010189876574677/181625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1445714553/100000000000000 : ℝ)*(base19) + (1568095047/100000000000000 : ℝ)*(base23) + (3279011/2000000000000 : ℝ)*(upper3) + (11757269/20000000000000 : ℝ)*(lower4) + (83215599/50000000000000 : ℝ)*(upper5) + (5917768163976613/100000000000000 : ℝ)*(major0) + (5917768163976613/100000000000000 : ℝ)*(major1) + (5917768163976613/100000000000000 : ℝ)*(major2) + (10028224093/25000000000000 : ℝ)*(sp1) + (42771929143/100000000000000 : ℝ)*(sp2) + (7920994758352231/100000000000000 : ℝ)*(sp4) + (7920953199741307/100000000000000 : ℝ)*(sp5) + (3960475209164021/50000000000000 : ℝ)*(sp6) + (978635326323803/25000000000000 : ℝ)*(sp7) + (978635326323803/25000000000000 : ℝ)*(f.failure) + (7920994758352231/100000000000000 : ℝ)*(f.sum) + (15232326304881/7265000000000000000000000000 : ℝ)*base65 + (3412067997500161147/363250000000000000000000000000000 : ℝ)*base68 + (1476475446920911147/363250000000000000000000000000000 : ℝ)*base70 + (3690252228740161147/363250000000000000000000000000000 : ℝ)*base72 + (45352255121771/7265000000000000000000000000 : ℝ)*base73 + (7950194715112161147/363250000000000000000000000000000 : ℝ)*base76 + (4188797390550911147/363250000000000000000000000000000 : ℝ)*base78 + (8502558344162661147/363250000000000000000000000000000 : ℝ)*base80 + (19040191315921/7265000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (27512561/2500000000000000000000 : ℝ)*base89 + (27512561/2500000000000000000000 : ℝ)*base91 + (27512561/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1229_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8421/2048 : ℝ) ≤ p) (hpb : p ≤ (4211/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151173987/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3559/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1133/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11437/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (113/800 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1229_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1229_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8421/2048 : ℝ) ≤ p) (hpb : p ≤ (4211/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151173987/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16257/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4723/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11437/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (113/800 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1229_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1229_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1229_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8421/2048 : ℝ) ≤ p) (hpb : p ≤ (4211/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151173987/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16257/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4723/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11437/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (113/800 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1229_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
