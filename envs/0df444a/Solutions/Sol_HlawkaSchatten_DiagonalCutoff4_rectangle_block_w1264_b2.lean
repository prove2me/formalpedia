-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1264_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:56:45.305324+00:00
-- url     : https://prove2.me/submissions/521e65aa-c474-49f7-963d-38260c6842da

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
theorem support_rectangle_w1264_s6_0 (p : ℝ) (hpa : (1057/256 : ℝ) ≤ p) (hpb : p ≤ (8457/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-421972371/2000000000 : ℝ)*x 0 + (2695476971/5000000000 : ℝ)*x 1 + (5267342869/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (421972371/2000000000 : ℝ)^8457 ≤ (6416363652703/50000000000000 : ℝ)^6409 := by
    have hnat : (421972371 : ℕ)^8457*50000000000000^6409 ≤ 6416363652703^6409*2000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      421972371 2000000000 6416363652703 50000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2695476971/5000000000 : ℝ)^8457 ≤ (44250603815129/100000000000000 : ℝ)^6409 := by
    have hnat : (2695476971 : ℕ)^8457*100000000000000^6409 ≤ 44250603815129^6409*5000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695476971 5000000000 44250603815129 100000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5267342869/10000000000 : ℝ)^8457 ≤ (536458360863/1250000000000 : ℝ)^6409 := by
    have hnat : (5267342869 : ℕ)^8457*1250000000000^6409 ≤ 536458360863^6409*10000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267342869 10000000000 536458360863 1250000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8457/2048 : ℝ)) 8457 6409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-421972371/2000000000 : ℝ), (2695476971/5000000000 : ℝ), (5267342869/10000000000 : ℝ)] ![(6416363652703/50000000000000 : ℝ), (44250603815129/100000000000000 : ℝ), (536458360863/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-421972371/2000000000 : ℝ)|^8457 ≤ (6416363652703/50000000000000 : ℝ)^6409
        have hw : |(-421972371/2000000000 : ℝ)|=(421972371/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2695476971/5000000000 : ℝ)|^8457 ≤ (44250603815129/100000000000000 : ℝ)^6409
        have hw : |(2695476971/5000000000 : ℝ)|=(2695476971/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5267342869/10000000000 : ℝ)|^8457 ≤ (536458360863/1250000000000 : ℝ)^6409
        have hw : |(5267342869/10000000000 : ℝ)|=(5267342869/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1264_s6_1 (p : ℝ) (hpa : (1057/256 : ℝ) ≤ p) (hpb : p ≤ (8457/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1336057879/2500000000 : ℝ)*x 0 + (-3394583/15625000 : ℝ)*x 1 + (5267342863/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336057879/2500000000 : ℝ)^8457 ≤ (10936310613947/25000000000000 : ℝ)^6409 := by
    have hnat : (1336057879 : ℕ)^8457*25000000000000^6409 ≤ 10936310613947^6409*2500000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336057879 2500000000 10936310613947 25000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3394583/15625000 : ℝ)^8457 ≤ (6669044361691/50000000000000 : ℝ)^6409 := by
    have hnat : (3394583 : ℕ)^8457*50000000000000^6409 ≤ 6669044361691^6409*15625000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3394583 15625000 6669044361691 50000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5267342863/10000000000 : ℝ)^8457 ≤ (10729167201133/25000000000000 : ℝ)^6409 := by
    have hnat : (5267342863 : ℕ)^8457*25000000000000^6409 ≤ 10729167201133^6409*10000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267342863 10000000000 10729167201133 25000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8457/2048 : ℝ)) 8457 6409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336057879/2500000000 : ℝ), (-3394583/15625000 : ℝ), (5267342863/10000000000 : ℝ)] ![(10936310613947/25000000000000 : ℝ), (6669044361691/50000000000000 : ℝ), (10729167201133/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336057879/2500000000 : ℝ)|^8457 ≤ (10936310613947/25000000000000 : ℝ)^6409
        have hw : |(1336057879/2500000000 : ℝ)|=(1336057879/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3394583/15625000 : ℝ)|^8457 ≤ (6669044361691/50000000000000 : ℝ)^6409
        have hw : |(-3394583/15625000 : ℝ)|=(3394583/15625000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5267342863/10000000000 : ℝ)|^8457 ≤ (10729167201133/25000000000000 : ℝ)^6409
        have hw : |(5267342863/10000000000 : ℝ)|=(5267342863/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1264_s6_2 (p : ℝ) (hpa : (1057/256 : ℝ) ≤ p) (hpb : p ≤ (8457/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672115761/5000000000 : ℝ)*x 0 + (5267342863/10000000000 : ℝ)*x 1 + (-271566639/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672115761/5000000000 : ℝ)^8457 ≤ (8749048504119/20000000000000 : ℝ)^6409 := by
    have hnat : (2672115761 : ℕ)^8457*20000000000000^6409 ≤ 8749048504119^6409*5000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672115761 5000000000 8749048504119 20000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5267342863/10000000000 : ℝ)^8457 ≤ (10729167201133/25000000000000 : ℝ)^6409 := by
    have hnat : (5267342863 : ℕ)^8457*25000000000000^6409 ≤ 10729167201133^6409*10000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267342863 10000000000 10729167201133 25000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (271566639/1250000000 : ℝ)^8457 ≤ (3334522164643/25000000000000 : ℝ)^6409 := by
    have hnat : (271566639 : ℕ)^8457*25000000000000^6409 ≤ 3334522164643^6409*1250000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      271566639 1250000000 3334522164643 25000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8457/2048 : ℝ)) 8457 6409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672115761/5000000000 : ℝ), (5267342863/10000000000 : ℝ), (-271566639/1250000000 : ℝ)] ![(8749048504119/20000000000000 : ℝ), (10729167201133/25000000000000 : ℝ), (3334522164643/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672115761/5000000000 : ℝ)|^8457 ≤ (8749048504119/20000000000000 : ℝ)^6409
        have hw : |(2672115761/5000000000 : ℝ)|=(2672115761/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5267342863/10000000000 : ℝ)|^8457 ≤ (10729167201133/25000000000000 : ℝ)^6409
        have hw : |(5267342863/10000000000 : ℝ)|=(5267342863/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-271566639/1250000000 : ℝ)|^8457 ≤ (3334522164643/25000000000000 : ℝ)^6409
        have hw : |(-271566639/1250000000 : ℝ)|=(271566639/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1264_s6_3 (p : ℝ) (hpa : (1057/256 : ℝ) ≤ p) (hpb : p ≤ (8457/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4347756447/10000000000 : ℝ)*x 0 + (2111805181/5000000000 : ℝ)*x 1 + (2237714887/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4347756447/10000000000 : ℝ)^8457 ≤ (4164689608789/12500000000000 : ℝ)^6409 := by
    have hnat : (4347756447 : ℕ)^8457*12500000000000^6409 ≤ 4164689608789^6409*10000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4347756447 10000000000 4164689608789 12500000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2111805181/5000000000 : ℝ)^8457 ≤ (32067926783163/100000000000000 : ℝ)^6409 := by
    have hnat : (2111805181 : ℕ)^8457*100000000000000^6409 ≤ 32067926783163^6409*5000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2111805181 5000000000 32067926783163 100000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2237714887/5000000000 : ℝ)^8457 ≤ (34614556334971/100000000000000 : ℝ)^6409 := by
    have hnat : (2237714887 : ℕ)^8457*100000000000000^6409 ≤ 34614556334971^6409*5000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2237714887 5000000000 34614556334971 100000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8457/2048 : ℝ)) 8457 6409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4347756447/10000000000 : ℝ), (2111805181/5000000000 : ℝ), (2237714887/5000000000 : ℝ)] ![(4164689608789/12500000000000 : ℝ), (32067926783163/100000000000000 : ℝ), (34614556334971/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4347756447/10000000000 : ℝ)|^8457 ≤ (4164689608789/12500000000000 : ℝ)^6409
        have hw : |(4347756447/10000000000 : ℝ)|=(4347756447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2111805181/5000000000 : ℝ)|^8457 ≤ (32067926783163/100000000000000 : ℝ)^6409
        have hw : |(2111805181/5000000000 : ℝ)|=(2111805181/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2237714887/5000000000 : ℝ)|^8457 ≤ (34614556334971/100000000000000 : ℝ)^6409
        have hw : |(2237714887/5000000000 : ℝ)|=(2237714887/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1264_s6_4 (p : ℝ) (hpa : (1057/256 : ℝ) ≤ p) (hpb : p ≤ (8457/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1054933521/5000000000 : ℝ)*x 0 + (5267654143/10000000000 : ℝ)*x 1 + (5390641117/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1054933521/5000000000 : ℝ)^8457 ≤ (12832768935503/100000000000000 : ℝ)^6409 := by
    have hnat : (1054933521 : ℕ)^8457*100000000000000^6409 ≤ 12832768935503^6409*5000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1054933521 5000000000 12832768935503 100000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5267654143/10000000000 : ℝ)^8457 ≤ (21460007748451/50000000000000 : ℝ)^6409 := by
    have hnat : (5267654143 : ℕ)^8457*50000000000000^6409 ≤ 21460007748451^6409*10000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267654143 10000000000 21460007748451 50000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5390641117/10000000000 : ℝ)^8457 ≤ (22123607776251/50000000000000 : ℝ)^6409 := by
    have hnat : (5390641117 : ℕ)^8457*50000000000000^6409 ≤ 22123607776251^6409*10000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390641117 10000000000 22123607776251 50000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8457/2048 : ℝ)) 8457 6409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1054933521/5000000000 : ℝ), (5267654143/10000000000 : ℝ), (5390641117/10000000000 : ℝ)] ![(12832768935503/100000000000000 : ℝ), (21460007748451/50000000000000 : ℝ), (22123607776251/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1054933521/5000000000 : ℝ)|^8457 ≤ (12832768935503/100000000000000 : ℝ)^6409
        have hw : |(-1054933521/5000000000 : ℝ)|=(1054933521/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5267654143/10000000000 : ℝ)|^8457 ≤ (21460007748451/50000000000000 : ℝ)^6409
        have hw : |(5267654143/10000000000 : ℝ)|=(5267654143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5390641117/10000000000 : ℝ)|^8457 ≤ (22123607776251/50000000000000 : ℝ)^6409
        have hw : |(5390641117/10000000000 : ℝ)|=(5390641117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1264_s6_5 (p : ℝ) (hpa : (1057/256 : ℝ) ≤ p) (hpb : p ≤ (8457/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (212505817/400000000 : ℝ)*x 0 + (-2049235701/10000000000 : ℝ)*x 1 + (2695319967/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (212505817/400000000 : ℝ)^8457 ≤ (21702198838409/50000000000000 : ℝ)^6409 := by
    have hnat : (212505817 : ℕ)^8457*50000000000000^6409 ≤ 21702198838409^6409*400000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212505817 400000000 21702198838409 50000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2049235701/10000000000 : ℝ)^8457 ≤ (385887486853/3125000000000 : ℝ)^6409 := by
    have hnat : (2049235701 : ℕ)^8457*3125000000000^6409 ≤ 385887486853^6409*10000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2049235701 10000000000 385887486853 3125000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2695319967/5000000000 : ℝ)^8457 ≤ (2212360136967/5000000000000 : ℝ)^6409 := by
    have hnat : (2695319967 : ℕ)^8457*5000000000000^6409 ≤ 2212360136967^6409*5000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695319967 5000000000 2212360136967 5000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8457/2048 : ℝ)) 8457 6409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(212505817/400000000 : ℝ), (-2049235701/10000000000 : ℝ), (2695319967/5000000000 : ℝ)] ![(21702198838409/50000000000000 : ℝ), (385887486853/3125000000000 : ℝ), (2212360136967/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(212505817/400000000 : ℝ)|^8457 ≤ (21702198838409/50000000000000 : ℝ)^6409
        have hw : |(212505817/400000000 : ℝ)|=(212505817/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2049235701/10000000000 : ℝ)|^8457 ≤ (385887486853/3125000000000 : ℝ)^6409
        have hw : |(-2049235701/10000000000 : ℝ)|=(2049235701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2695319967/5000000000 : ℝ)|^8457 ≤ (2212360136967/5000000000000 : ℝ)^6409
        have hw : |(2695319967/5000000000 : ℝ)|=(2695319967/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1264_s6_6 (p : ℝ) (hpa : (1057/256 : ℝ) ≤ p) (hpb : p ≤ (8457/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1328160899/2500000000 : ℝ)*x 0 + (215625601/400000000 : ℝ)*x 1 + (-409847611/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328160899/2500000000 : ℝ)^8457 ≤ (10851094489707/25000000000000 : ℝ)^6409 := by
    have hnat : (1328160899 : ℕ)^8457*25000000000000^6409 ≤ 10851094489707^6409*2500000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328160899 2500000000 10851094489707 25000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (215625601/400000000 : ℝ)^8457 ≤ (5530900465621/12500000000000 : ℝ)^6409 := by
    have hnat : (215625601 : ℕ)^8457*12500000000000^6409 ≤ 5530900465621^6409*400000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215625601 400000000 5530900465621 12500000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (409847611/2000000000 : ℝ)^8457 ≤ (12348418296947/100000000000000 : ℝ)^6409 := by
    have hnat : (409847611 : ℕ)^8457*100000000000000^6409 ≤ 12348418296947^6409*2000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      409847611 2000000000 12348418296947 100000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8457/2048 : ℝ)) 8457 6409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1328160899/2500000000 : ℝ), (215625601/400000000 : ℝ), (-409847611/2000000000 : ℝ)] ![(10851094489707/25000000000000 : ℝ), (5530900465621/12500000000000 : ℝ), (12348418296947/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1328160899/2500000000 : ℝ)|^8457 ≤ (10851094489707/25000000000000 : ℝ)^6409
        have hw : |(1328160899/2500000000 : ℝ)|=(1328160899/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(215625601/400000000 : ℝ)|^8457 ≤ (5530900465621/12500000000000 : ℝ)^6409
        have hw : |(215625601/400000000 : ℝ)|=(215625601/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-409847611/2000000000 : ℝ)|^8457 ≤ (12348418296947/100000000000000 : ℝ)^6409
        have hw : |(-409847611/2000000000 : ℝ)|=(409847611/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1264_s6_7 (p : ℝ) (hpa : (1057/256 : ℝ) ≤ p) (hpb : p ≤ (8457/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2173882703/5000000000 : ℝ)*x 0 + (873983/1953125 : ℝ)*x 1 + (4224249997/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2173882703/5000000000 : ℝ)^8457 ≤ (16658803731501/50000000000000 : ℝ)^6409 := by
    have hnat : (2173882703 : ℕ)^8457*50000000000000^6409 ≤ 16658803731501^6409*5000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2173882703 5000000000 16658803731501 50000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (873983/1953125 : ℝ)^8457 ≤ (34608057241093/100000000000000 : ℝ)^6409 := by
    have hnat : (873983 : ℕ)^8457*100000000000000^6409 ≤ 34608057241093^6409*1953125^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      873983 1953125 34608057241093 100000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4224249997/10000000000 : ℝ)^8457 ≤ (32074335274823/100000000000000 : ℝ)^6409 := by
    have hnat : (4224249997 : ℕ)^8457*100000000000000^6409 ≤ 32074335274823^6409*10000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4224249997 10000000000 32074335274823 100000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8457/2048 : ℝ)) 8457 6409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2173882703/5000000000 : ℝ), (873983/1953125 : ℝ), (4224249997/10000000000 : ℝ)] ![(16658803731501/50000000000000 : ℝ), (34608057241093/100000000000000 : ℝ), (32074335274823/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2173882703/5000000000 : ℝ)|^8457 ≤ (16658803731501/50000000000000 : ℝ)^6409
        have hw : |(2173882703/5000000000 : ℝ)|=(2173882703/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(873983/1953125 : ℝ)|^8457 ≤ (34608057241093/100000000000000 : ℝ)^6409
        have hw : |(873983/1953125 : ℝ)|=(873983/1953125 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4224249997/10000000000 : ℝ)|^8457 ≤ (32074335274823/100000000000000 : ℝ)^6409
        have hw : |(4224249997/10000000000 : ℝ)|=(4224249997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1264_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1057/256 : ℝ) ≤ p) (hpb : p ≤ (8457/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151859563/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14139/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5741/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (11501/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (353/2500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14139/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5741/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14139/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5741/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14139/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5741/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14139/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5741/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14139/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5741/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14139/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5741/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5741/50000 : ℝ) ^ (1057/256 : ℝ) ≤ (82182731886103/625000000000000000 : ℝ) := by
    have hpowers : (5741/50000 : ℝ)^1057 ≤ (82182731886103/625000000000000000 : ℝ)^256 := by
      have hnat : (5741 : ℕ)^1057*625000000000000000^256 ≤ 82182731886103^256*50000^1057 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5741 50000 82182731886103 625000000000000000 1057 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5741/50000 : ℝ)) (X := (82182731886103/625000000000000000 : ℝ)) (by norm_num) (by norm_num) 1057 256 (by norm_num) hpowers
    exact h
  have hpowhi : (14139/100000 : ℝ) ^ (1057/256 : ℝ) ≤ (31056923890218471/100000000000000000000 : ℝ) := by
    have hpowers : (14139/100000 : ℝ)^1057 ≤ (31056923890218471/100000000000000000000 : ℝ)^256 := by
      have hnat : (14139 : ℕ)^1057*100000000000000000000^256 ≤ 31056923890218471^256*100000^1057 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14139 100000 31056923890218471 100000000000000000000 1057 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14139/100000 : ℝ)) (X := (31056923890218471/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1057 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (312582182731886103/312500000000000000 : ℝ) ≤ (10000636872151803/10000000000000000 : ℝ) ^ (1057/256 : ℝ) := by
    have hpowers : (312582182731886103/312500000000000000 : ℝ)^256 ≤ (10000636872151803/10000000000000000 : ℝ)^1057 := by
      have hnat : (312582182731886103 : ℕ)^256*10000000000000000^1057 ≤ 10000636872151803^1057*312500000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        312582182731886103 312500000000000000 10000636872151803 10000000000000000 256 1057 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000636872151803/10000000000000000 : ℝ)) (X := (312582182731886103/312500000000000000 : ℝ)) (by norm_num) 1057 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (100044206160991994951/100000000000000000000 : ℝ) ≤ (5000535235674747/5000000000000000 : ℝ) ^ (1057/256 : ℝ) := by
    have hpowers : (100044206160991994951/100000000000000000000 : ℝ)^256 ≤ (5000535235674747/5000000000000000 : ℝ)^1057 := by
      have hnat : (100044206160991994951 : ℕ)^256*5000000000000000^1057 ≤ 5000535235674747^1057*100000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100044206160991994951 100000000000000000000 5000535235674747 5000000000000000 256 1057 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000535235674747/5000000000000000 : ℝ)) (X := (100044206160991994951/100000000000000000000 : ℝ)) (by norm_num) 1057 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (50031056923890218471/50000000000000000000 : ℝ) ≤ (2000300814109437/2000000000000000 : ℝ) ^ (1057/256 : ℝ) := by
    have hpowers : (50031056923890218471/50000000000000000000 : ℝ)^256 ≤ (2000300814109437/2000000000000000 : ℝ)^1057 := by
      have hnat : (50031056923890218471 : ℕ)^256*2000000000000000^1057 ≤ 2000300814109437^1057*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50031056923890218471 50000000000000000000 2000300814109437 2000000000000000 256 1057 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000300814109437/2000000000000000 : ℝ)) (X := (50031056923890218471/50000000000000000000 : ℝ)) (by norm_num) 1057 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(82182731886103/625000000000000000 : ℝ) ≤ ((26561734997331564447/26570000000000000000 : ℝ)+2*(433599197691/265700000000000 : ℝ)*(5741/50000 : ℝ))^(1057/256 : ℝ) := by
    rw [show (26561734997331564447/26570000000000000000 : ℝ)+2*(433599197691/265700000000000 : ℝ)*(5741/50000 : ℝ)=(10000636872151803/10000000000000000 : ℝ) by norm_num, show 1+2*(82182731886103/625000000000000000 : ℝ)=(312582182731886103/312500000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(31056923890218471/100000000000000000000 : ℝ)+(82182731886103/625000000000000000 : ℝ) ≤ ((26561734997331564447/26570000000000000000 : ℝ)+(433599197691/265700000000000 : ℝ)*((14139/100000 : ℝ)+(5741/50000 : ℝ)))^(1057/256 : ℝ) := by
    rw [show (26561734997331564447/26570000000000000000 : ℝ)+(433599197691/265700000000000 : ℝ)*((14139/100000 : ℝ)+(5741/50000 : ℝ))=(5000535235674747/5000000000000000 : ℝ) by norm_num, show 1+(31056923890218471/100000000000000000000 : ℝ)+(82182731886103/625000000000000000 : ℝ)=(100044206160991994951/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(31056923890218471/100000000000000000000 : ℝ) ≤ ((26561734997331564447/26570000000000000000 : ℝ)+2*(433599197691/265700000000000 : ℝ)*(14139/100000 : ℝ))^(1057/256 : ℝ) := by
    rw [show (26561734997331564447/26570000000000000000 : ℝ)+2*(433599197691/265700000000000 : ℝ)*(14139/100000 : ℝ)=(2000300814109437/2000000000000000 : ℝ) by norm_num, show 1+2*(31056923890218471/100000000000000000000 : ℝ)=(50031056923890218471/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (26561734997331564447/26570000000000000000 : ℝ)*(X 1 0+X 2 0)+(433599197691/265700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1057/256 : ℝ)) (lo := (5741/50000 : ℝ)) (hi := (14139/100000 : ℝ)) (c := (26561734997331564447/26570000000000000000 : ℝ)) (alpha := (433599197691/265700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (26561734997331564447/26570000000000000000 : ℝ)*(X 0 1+X 2 1)+(433599197691/265700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1057/256 : ℝ)) (lo := (5741/50000 : ℝ)) (hi := (14139/100000 : ℝ)) (c := (26561734997331564447/26570000000000000000 : ℝ)) (alpha := (433599197691/265700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (26561734997331564447/26570000000000000000 : ℝ)*(X 0 2+X 1 2)+(433599197691/265700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1057/256 : ℝ)) (lo := (5741/50000 : ℝ)) (hi := (14139/100000 : ℝ)) (c := (26561734997331564447/26570000000000000000 : ℝ)) (alpha := (433599197691/265700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-421972371/2000000000 : ℝ)*X 0 0+(2695476971/5000000000 : ℝ)*X 0 1+(5267342869/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1264_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1336057879/2500000000 : ℝ)*X 1 0+(-3394583/15625000 : ℝ)*X 1 1+(5267342863/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1264_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672115761/5000000000 : ℝ)*X 2 0+(5267342863/10000000000 : ℝ)*X 2 1+(-271566639/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1264_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4347756447/10000000000 : ℝ)*X 0 0+(2111805181/5000000000 : ℝ)*X 0 1+(2237714887/5000000000 : ℝ)*X 0 2+(4347756447/10000000000 : ℝ)*X 1 0+(2111805181/5000000000 : ℝ)*X 1 1+(2237714887/5000000000 : ℝ)*X 1 2+(4347756447/10000000000 : ℝ)*X 2 0+(2111805181/5000000000 : ℝ)*X 2 1+(2237714887/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1264_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1054933521/5000000000 : ℝ)*X 0 0+(5267654143/10000000000 : ℝ)*X 0 1+(5390641117/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1264_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((212505817/400000000 : ℝ)*X 1 0+(-2049235701/10000000000 : ℝ)*X 1 1+(2695319967/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1264_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1328160899/2500000000 : ℝ)*X 2 0+(215625601/400000000 : ℝ)*X 2 1+(-409847611/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1264_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2173882703/5000000000 : ℝ)*X 0 0+(873983/1953125 : ℝ)*X 0 1+(4224249997/10000000000 : ℝ)*X 0 2+(2173882703/5000000000 : ℝ)*X 1 0+(873983/1953125 : ℝ)*X 1 1+(4224249997/10000000000 : ℝ)*X 1 2+(2173882703/5000000000 : ℝ)*X 2 0+(873983/1953125 : ℝ)*X 2 1+(4224249997/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1264_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (11174956368460378131717/1660625000000000000000000000 : ℝ) := by norm_num
    linear_combination (327885651/25000000000000 : ℝ)*(base19) + (1226827769/100000000000000 : ℝ)*(base23) + (12531887/25000000000000 : ℝ)*(lower2) + (41736783/25000000000000 : ℝ)*(upper3) + (113058183/100000000000000 : ℝ)*(upper5) + (753818773798791/12500000000000 : ℝ)*(major0) + (753818773798791/12500000000000 : ℝ)*(major1) + (753818773798791/12500000000000 : ℝ)*(major2) + (2022481868797971/25000000000000 : ℝ)*(sp0) + (1617992514374879/20000000000000 : ℝ)*(sp1) + (8089962656589231/100000000000000 : ℝ)*(sp2) + (1985558560952797/50000000000000 : ℝ)*(sp3) + (9102056279/25000000000000 : ℝ)*(sp4) + (4787786449/25000000000000 : ℝ)*(sp7) + (397113627305139/10000000000000 : ℝ)*(f.failure) + (8089963883416999/100000000000000 : ℝ)*(f.sum) + (12176144648039/6642500000000000000000000000 : ℝ)*base65 + (744891435880716423/332125000000000000000000000000000 : ℝ)*base68 + (295070110716283577/332125000000000000000000000000000 : ℝ)*base69 + (1048721714076966423/332125000000000000000000000000000 : ℝ)*base72 + (29559942766483/3321250000000000000000000000 : ℝ)*base74 + (4566223145482658577/332125000000000000000000000000000 : ℝ)*base75 + (1487548602593783577/332125000000000000000000000000000 : ℝ)*base77 + (744973150919341423/332125000000000000000000000000000 : ℝ)*base80 + (321041216143/830312500000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (3805743/1000000000000000000000 : ℝ)*base90 + (3805743/1000000000000000000000 : ℝ)*base92 + (3805743/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (16250428874493440285797382613/1328500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (303079859/50000000000000 : ℝ)*(base19) + (194386139/20000000000000 : ℝ)*(upper2) + (77587439/10000000000000 : ℝ)*(upper3) + (209533113/50000000000000 : ℝ)*(lower4) + (6061292823165331/100000000000000 : ℝ)*(major0) + (6061292823165331/100000000000000 : ℝ)*(major1) + (6061292823165331/100000000000000 : ℝ)*(major2) + (11861131497/6250000000000 : ℝ)*(sp0) + (35748444047/50000000000000 : ℝ)*(sp1) + (16003517863/50000000000000 : ℝ)*(sp3) + (8131015067034969/100000000000000 : ℝ)*(sp4) + (2032783185522777/25000000000000 : ℝ)*(sp5) + (203280121128473/2500000000000 : ℝ)*(sp6) + (159653935456689/4000000000000 : ℝ)*(sp7) + (79827607869059/2000000000000 : ℝ)*(f.failure) + (203280121128473/2500000000000 : ℝ)*(f.sum) + (247926908322731/13285000000000000000000000000 : ℝ)*base65 + (49517909537256313043/2657000000000000000000000000000000 : ℝ)*base68 + (57038571278035313043/2657000000000000000000000000000000 : ℝ)*base70 + (38450869814497313043/2657000000000000000000000000000000 : ℝ)*base72 + (4487153223881/13285000000000000000000000000 : ℝ)*base73 + (54422864599816313043/2657000000000000000000000000000000 : ℝ)*base76 + (4810605876309313043/2657000000000000000000000000000000 : ℝ)*base78 + (66358952380649313043/2657000000000000000000000000000000 : ℝ)*base80 + (13192449881561/3321250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1038783/200000000000000000000 : ℝ)*base90 + (1038783/200000000000000000000 : ℝ)*base92 + (1038783/200000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1264_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1057/256 : ℝ) ≤ p) (hpb : p ≤ (8457/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151859563/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14139/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5741/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11501/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (353/2500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1264_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1264_s7_0 (p : ℝ) (hpa : (1057/256 : ℝ) ≤ p) (hpb : p ≤ (8457/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2109874243/10000000000 : ℝ)*x 0 + (5390779599/10000000000 : ℝ)*x 1 + (5267509259/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2109874243/10000000000 : ℝ)^8457 ≤ (12832826729721/100000000000000 : ℝ)^6409 := by
    have hnat : (2109874243 : ℕ)^8457*100000000000000^6409 ≤ 12832826729721^6409*10000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2109874243 10000000000 12832826729721 100000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5390779599/10000000000 : ℝ)^8457 ≤ (2765544716729/6250000000000 : ℝ)^6409 := by
    have hnat : (5390779599 : ℕ)^8457*6250000000000^6409 ≤ 2765544716729^6409*10000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390779599 10000000000 2765544716729 6250000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5267509259/10000000000 : ℝ)^8457 ≤ (8583691556959/20000000000000 : ℝ)^6409 := by
    have hnat : (5267509259 : ℕ)^8457*20000000000000^6409 ≤ 8583691556959^6409*10000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267509259 10000000000 8583691556959 20000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8457/2048 : ℝ)) 8457 6409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2109874243/10000000000 : ℝ), (5390779599/10000000000 : ℝ), (5267509259/10000000000 : ℝ)] ![(12832826729721/100000000000000 : ℝ), (2765544716729/6250000000000 : ℝ), (8583691556959/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2109874243/10000000000 : ℝ)|^8457 ≤ (12832826729721/100000000000000 : ℝ)^6409
        have hw : |(-2109874243/10000000000 : ℝ)|=(2109874243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5390779599/10000000000 : ℝ)|^8457 ≤ (2765544716729/6250000000000 : ℝ)^6409
        have hw : |(5390779599/10000000000 : ℝ)|=(5390779599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5267509259/10000000000 : ℝ)|^8457 ≤ (8583691556959/20000000000000 : ℝ)^6409
        have hw : |(5267509259/10000000000 : ℝ)|=(5267509259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1264_s7_1 (p : ℝ) (hpa : (1057/256 : ℝ) ≤ p) (hpb : p ≤ (8457/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344187957/10000000000 : ℝ)*x 0 + (-54309259/250000000 : ℝ)*x 1 + (329219329/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344187957/10000000000 : ℝ)^8457 ≤ (43744771967347/100000000000000 : ℝ)^6409 := by
    have hnat : (5344187957 : ℕ)^8457*100000000000000^6409 ≤ 43744771967347^6409*10000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344187957 10000000000 43744771967347 100000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (54309259/250000000 : ℝ)^8457 ≤ (1333677017601/10000000000000 : ℝ)^6409 := by
    have hnat : (54309259 : ℕ)^8457*10000000000000^6409 ≤ 1333677017601^6409*250000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      54309259 250000000 1333677017601 10000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (329219329/625000000 : ℝ)^8457 ≤ (5364807229819/12500000000000 : ℝ)^6409 := by
    have hnat : (329219329 : ℕ)^8457*12500000000000^6409 ≤ 5364807229819^6409*625000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      329219329 625000000 5364807229819 12500000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8457/2048 : ℝ)) 8457 6409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344187957/10000000000 : ℝ), (-54309259/250000000 : ℝ), (329219329/625000000 : ℝ)] ![(43744771967347/100000000000000 : ℝ), (1333677017601/10000000000000 : ℝ), (5364807229819/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344187957/10000000000 : ℝ)|^8457 ≤ (43744771967347/100000000000000 : ℝ)^6409
        have hw : |(5344187957/10000000000 : ℝ)|=(5344187957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-54309259/250000000 : ℝ)|^8457 ≤ (1333677017601/10000000000000 : ℝ)^6409
        have hw : |(-54309259/250000000 : ℝ)|=(54309259/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(329219329/625000000 : ℝ)|^8457 ≤ (5364807229819/12500000000000 : ℝ)^6409
        have hw : |(329219329/625000000 : ℝ)|=(329219329/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1264_s7_2 (p : ℝ) (hpa : (1057/256 : ℝ) ≤ p) (hpb : p ≤ (8457/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344187957/10000000000 : ℝ)*x 0 + (526750927/1000000000 : ℝ)*x 1 + (-135773147/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344187957/10000000000 : ℝ)^8457 ≤ (43744771967347/100000000000000 : ℝ)^6409 := by
    have hnat : (5344187957 : ℕ)^8457*100000000000000^6409 ≤ 43744771967347^6409*10000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344187957 10000000000 43744771967347 100000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (526750927/1000000000 : ℝ)^8457 ≤ (42918457903061/100000000000000 : ℝ)^6409 := by
    have hnat : (526750927 : ℕ)^8457*100000000000000^6409 ≤ 42918457903061^6409*1000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526750927 1000000000 42918457903061 100000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (135773147/625000000 : ℝ)^8457 ≤ (13336770111201/100000000000000 : ℝ)^6409 := by
    have hnat : (135773147 : ℕ)^8457*100000000000000^6409 ≤ 13336770111201^6409*625000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135773147 625000000 13336770111201 100000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8457/2048 : ℝ)) 8457 6409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344187957/10000000000 : ℝ), (526750927/1000000000 : ℝ), (-135773147/625000000 : ℝ)] ![(43744771967347/100000000000000 : ℝ), (42918457903061/100000000000000 : ℝ), (13336770111201/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344187957/10000000000 : ℝ)|^8457 ≤ (43744771967347/100000000000000 : ℝ)^6409
        have hw : |(5344187957/10000000000 : ℝ)|=(5344187957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(526750927/1000000000 : ℝ)|^8457 ≤ (42918457903061/100000000000000 : ℝ)^6409
        have hw : |(526750927/1000000000 : ℝ)|=(526750927/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-135773147/625000000 : ℝ)|^8457 ≤ (13336770111201/100000000000000 : ℝ)^6409
        have hw : |(-135773147/625000000 : ℝ)|=(135773147/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1264_s7_3 (p : ℝ) (hpa : (1057/256 : ℝ) ≤ p) (hpb : p ≤ (8457/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (86955301/200000000 : ℝ)*x 0 + (2111978183/5000000000 : ℝ)*x 1 + (2237540791/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (86955301/200000000 : ℝ)^8457 ≤ (16658801931579/50000000000000 : ℝ)^6409 := by
    have hnat : (86955301 : ℕ)^8457*50000000000000^6409 ≤ 16658801931579^6409*200000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      86955301 200000000 16658801931579 50000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2111978183/5000000000 : ℝ)^8457 ≤ (16035696676283/50000000000000 : ℝ)^6409 := by
    have hnat : (2111978183 : ℕ)^8457*50000000000000^6409 ≤ 16035696676283^6409*5000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2111978183 5000000000 16035696676283 50000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2237540791/5000000000 : ℝ)^8457 ≤ (8652750694113/25000000000000 : ℝ)^6409 := by
    have hnat : (2237540791 : ℕ)^8457*25000000000000^6409 ≤ 8652750694113^6409*5000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2237540791 5000000000 8652750694113 25000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8457/2048 : ℝ)) 8457 6409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(86955301/200000000 : ℝ), (2111978183/5000000000 : ℝ), (2237540791/5000000000 : ℝ)] ![(16658801931579/50000000000000 : ℝ), (16035696676283/50000000000000 : ℝ), (8652750694113/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(86955301/200000000 : ℝ)|^8457 ≤ (16658801931579/50000000000000 : ℝ)^6409
        have hw : |(86955301/200000000 : ℝ)|=(86955301/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2111978183/5000000000 : ℝ)|^8457 ≤ (16035696676283/50000000000000 : ℝ)^6409
        have hw : |(2111978183/5000000000 : ℝ)|=(2111978183/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2237540791/5000000000 : ℝ)|^8457 ≤ (8652750694113/25000000000000 : ℝ)^6409
        have hw : |(2237540791/5000000000 : ℝ)|=(2237540791/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1264_s7_4 (p : ℝ) (hpa : (1057/256 : ℝ) ≤ p) (hpb : p ≤ (8457/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2109879067/10000000000 : ℝ)*x 0 + (526781987/1000000000 : ℝ)*x 1 + (336904231/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2109879067/10000000000 : ℝ)^8457 ≤ (2566573089301/20000000000000 : ℝ)^6409 := by
    have hnat : (2109879067 : ℕ)^8457*20000000000000^6409 ≤ 2566573089301^6409*10000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2109879067 10000000000 2566573089301 20000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (526781987/1000000000 : ℝ)^8457 ≤ (2682612332383/6250000000000 : ℝ)^6409 := by
    have hnat : (526781987 : ℕ)^8457*6250000000000^6409 ≤ 2682612332383^6409*1000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526781987 1000000000 2682612332383 6250000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (336904231/625000000 : ℝ)^8457 ≤ (44245337226203/100000000000000 : ℝ)^6409 := by
    have hnat : (336904231 : ℕ)^8457*100000000000000^6409 ≤ 44245337226203^6409*625000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      336904231 625000000 44245337226203 100000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8457/2048 : ℝ)) 8457 6409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2109879067/10000000000 : ℝ), (526781987/1000000000 : ℝ), (336904231/625000000 : ℝ)] ![(2566573089301/20000000000000 : ℝ), (2682612332383/6250000000000 : ℝ), (44245337226203/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2109879067/10000000000 : ℝ)|^8457 ≤ (2566573089301/20000000000000 : ℝ)^6409
        have hw : |(-2109879067/10000000000 : ℝ)|=(2109879067/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(526781987/1000000000 : ℝ)|^8457 ≤ (2682612332383/6250000000000 : ℝ)^6409
        have hw : |(526781987/1000000000 : ℝ)|=(526781987/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(336904231/625000000 : ℝ)|^8457 ≤ (44245337226203/100000000000000 : ℝ)^6409
        have hw : |(336904231/625000000 : ℝ)|=(336904231/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1264_s7_5 (p : ℝ) (hpa : (1057/256 : ℝ) ≤ p) (hpb : p ≤ (8457/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (664086101/1250000000 : ℝ)*x 0 + (-2049412147/10000000000 : ℝ)*x 1 + (1078093443/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (664086101/1250000000 : ℝ)^8457 ≤ (43404865378691/100000000000000 : ℝ)^6409 := by
    have hnat : (664086101 : ℕ)^8457*100000000000000^6409 ≤ 43404865378691^6409*1250000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      664086101 1250000000 43404865378691 100000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2049412147/10000000000 : ℝ)^8457 ≤ (12349802595257/100000000000000 : ℝ)^6409 := by
    have hnat : (2049412147 : ℕ)^8457*100000000000000^6409 ≤ 12349802595257^6409*10000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2049412147 10000000000 12349802595257 100000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1078093443/2000000000 : ℝ)^8457 ≤ (44245332016509/100000000000000 : ℝ)^6409 := by
    have hnat : (1078093443 : ℕ)^8457*100000000000000^6409 ≤ 44245332016509^6409*2000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078093443 2000000000 44245332016509 100000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8457/2048 : ℝ)) 8457 6409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(664086101/1250000000 : ℝ), (-2049412147/10000000000 : ℝ), (1078093443/2000000000 : ℝ)] ![(43404865378691/100000000000000 : ℝ), (12349802595257/100000000000000 : ℝ), (44245332016509/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(664086101/1250000000 : ℝ)|^8457 ≤ (43404865378691/100000000000000 : ℝ)^6409
        have hw : |(664086101/1250000000 : ℝ)|=(664086101/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2049412147/10000000000 : ℝ)|^8457 ≤ (12349802595257/100000000000000 : ℝ)^6409
        have hw : |(-2049412147/10000000000 : ℝ)|=(2049412147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1078093443/2000000000 : ℝ)|^8457 ≤ (44245332016509/100000000000000 : ℝ)^6409
        have hw : |(1078093443/2000000000 : ℝ)|=(1078093443/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1264_s7_6 (p : ℝ) (hpa : (1057/256 : ℝ) ≤ p) (hpb : p ≤ (8457/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2656344431/5000000000 : ℝ)*x 0 + (673808391/1250000000 : ℝ)*x 1 + (-2049412191/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656344431/5000000000 : ℝ)^8457 ≤ (43404865960853/100000000000000 : ℝ)^6409 := by
    have hnat : (2656344431 : ℕ)^8457*100000000000000^6409 ≤ 43404865960853^6409*5000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656344431 5000000000 43404865960853 100000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (673808391/1250000000 : ℝ)^8457 ≤ (8849066214843/20000000000000 : ℝ)^6409 := by
    have hnat : (673808391 : ℕ)^8457*20000000000000^6409 ≤ 8849066214843^6409*1250000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      673808391 1250000000 8849066214843 20000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2049412191/10000000000 : ℝ)^8457 ≤ (1234980294513/10000000000000 : ℝ)^6409 := by
    have hnat : (2049412191 : ℕ)^8457*10000000000000^6409 ≤ 1234980294513^6409*10000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2049412191 10000000000 1234980294513 10000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8457/2048 : ℝ)) 8457 6409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656344431/5000000000 : ℝ), (673808391/1250000000 : ℝ), (-2049412191/10000000000 : ℝ)] ![(43404865960853/100000000000000 : ℝ), (8849066214843/20000000000000 : ℝ), (1234980294513/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656344431/5000000000 : ℝ)|^8457 ≤ (43404865960853/100000000000000 : ℝ)^6409
        have hw : |(2656344431/5000000000 : ℝ)|=(2656344431/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(673808391/1250000000 : ℝ)|^8457 ≤ (8849066214843/20000000000000 : ℝ)^6409
        have hw : |(673808391/1250000000 : ℝ)|=(673808391/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2049412191/10000000000 : ℝ)|^8457 ≤ (1234980294513/10000000000000 : ℝ)^6409
        have hw : |(-2049412191/10000000000 : ℝ)|=(2049412191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1264_s7_7 (p : ℝ) (hpa : (1057/256 : ℝ) ≤ p) (hpb : p ≤ (8457/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1086943613/2500000000 : ℝ)*x 0 + (111861191/250000000 : ℝ)*x 1 + (1056148149/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1086943613/2500000000 : ℝ)^8457 ≤ (3331769893549/10000000000000 : ℝ)^6409 := by
    have hnat : (1086943613 : ℕ)^8457*10000000000000^6409 ≤ 3331769893549^6409*2500000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1086943613 2500000000 3331769893549 10000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (111861191/250000000 : ℝ)^8457 ≤ (34604533153369/100000000000000 : ℝ)^6409 := by
    have hnat : (111861191 : ℕ)^8457*100000000000000^6409 ≤ 34604533153369^6409*250000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      111861191 250000000 34604533153369 100000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1056148149/2500000000 : ℝ)^8457 ≤ (32077767895623/100000000000000 : ℝ)^6409 := by
    have hnat : (1056148149 : ℕ)^8457*100000000000000^6409 ≤ 32077767895623^6409*2500000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056148149 2500000000 32077767895623 100000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8457/2048 : ℝ)) 8457 6409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1086943613/2500000000 : ℝ), (111861191/250000000 : ℝ), (1056148149/2500000000 : ℝ)] ![(3331769893549/10000000000000 : ℝ), (34604533153369/100000000000000 : ℝ), (32077767895623/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1086943613/2500000000 : ℝ)|^8457 ≤ (3331769893549/10000000000000 : ℝ)^6409
        have hw : |(1086943613/2500000000 : ℝ)|=(1086943613/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(111861191/250000000 : ℝ)|^8457 ≤ (34604533153369/100000000000000 : ℝ)^6409
        have hw : |(111861191/250000000 : ℝ)|=(111861191/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1056148149/2500000000 : ℝ)|^8457 ≤ (32077767895623/100000000000000 : ℝ)^6409
        have hw : |(1056148149/2500000000 : ℝ)|=(1056148149/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1264_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1057/256 : ℝ) ≤ p) (hpb : p ≤ (8457/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151859563/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (353/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11501/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2301/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3529/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (353/2500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11501/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (353/2500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11501/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (353/2500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11501/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (353/2500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11501/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (353/2500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11501/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (353/2500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11501/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11501/100000 : ℝ) ^ (1057/256 : ℝ) ≤ (13239310345609037/100000000000000000000 : ℝ) := by
    have hpowers : (11501/100000 : ℝ)^1057 ≤ (13239310345609037/100000000000000000000 : ℝ)^256 := by
      have hnat : (11501 : ℕ)^1057*100000000000000000000^256 ≤ 13239310345609037^256*100000^1057 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11501 100000 13239310345609037 100000000000000000000 1057 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11501/100000 : ℝ)) (X := (13239310345609037/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1057 256 (by norm_num) hpowers
    exact h
  have hpowhi : (353/2500 : ℝ) ^ (1057/256 : ℝ) ≤ (7721242178435609/25000000000000000000 : ℝ) := by
    have hpowers : (353/2500 : ℝ)^1057 ≤ (7721242178435609/25000000000000000000 : ℝ)^256 := by
      have hnat : (353 : ℕ)^1057*25000000000000000000^256 ≤ 7721242178435609^256*2500^1057 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        353 2500 7721242178435609 25000000000000000000 1057 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (353/2500 : ℝ)) (X := (7721242178435609/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1057 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013239310345609037/50000000000000000000 : ℝ) ≤ (10000641234335407/10000000000000000 : ℝ) ^ (1057/256 : ℝ) := by
    have hpowers : (50013239310345609037/50000000000000000000 : ℝ)^256 ≤ (10000641234335407/10000000000000000 : ℝ)^1057 := by
      have hnat : (50013239310345609037 : ℕ)^256*10000000000000000^1057 ≤ 10000641234335407^1057*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013239310345609037 50000000000000000000 10000641234335407 10000000000000000 256 1057 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000641234335407/10000000000000000 : ℝ)) (X := (50013239310345609037/50000000000000000000 : ℝ)) (by norm_num) 1057 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (100044124279059351473/100000000000000000000 : ℝ) ≤ (10001068488874389/10000000000000000 : ℝ) ^ (1057/256 : ℝ) := by
    have hpowers : (100044124279059351473/100000000000000000000 : ℝ)^256 ≤ (10001068488874389/10000000000000000 : ℝ)^1057 := by
      have hnat : (100044124279059351473 : ℕ)^256*10000000000000000^1057 ≤ 10001068488874389^1057*100000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100044124279059351473 100000000000000000000 10001068488874389 10000000000000000 256 1057 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001068488874389/10000000000000000 : ℝ)) (X := (100044124279059351473/100000000000000000000 : ℝ)) (by norm_num) 1057 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (12507721242178435609/12500000000000000000 : ℝ) ≤ (10001495743413371/10000000000000000 : ℝ) ^ (1057/256 : ℝ) := by
    have hpowers : (12507721242178435609/12500000000000000000 : ℝ)^256 ≤ (10001495743413371/10000000000000000 : ℝ)^1057 := by
      have hnat : (12507721242178435609 : ℕ)^256*10000000000000000^1057 ≤ 10001495743413371^1057*12500000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12507721242178435609 12500000000000000000 10001495743413371 10000000000000000 256 1057 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001495743413371/10000000000000000 : ℝ)) (X := (12507721242178435609/12500000000000000000 : ℝ)) (by norm_num) 1057 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13239310345609037/100000000000000000000 : ℝ) ≤ ((26181851683818766969/26190000000000000000 : ℝ)+2*(213627269491/130950000000000 : ℝ)*(11501/100000 : ℝ))^(1057/256 : ℝ) := by
    rw [show (26181851683818766969/26190000000000000000 : ℝ)+2*(213627269491/130950000000000 : ℝ)*(11501/100000 : ℝ)=(10000641234335407/10000000000000000 : ℝ) by norm_num, show 1+2*(13239310345609037/100000000000000000000 : ℝ)=(50013239310345609037/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(7721242178435609/25000000000000000000 : ℝ)+(13239310345609037/100000000000000000000 : ℝ) ≤ ((26181851683818766969/26190000000000000000 : ℝ)+(213627269491/130950000000000 : ℝ)*((353/2500 : ℝ)+(11501/100000 : ℝ)))^(1057/256 : ℝ) := by
    rw [show (26181851683818766969/26190000000000000000 : ℝ)+(213627269491/130950000000000 : ℝ)*((353/2500 : ℝ)+(11501/100000 : ℝ))=(10001068488874389/10000000000000000 : ℝ) by norm_num, show 1+(7721242178435609/25000000000000000000 : ℝ)+(13239310345609037/100000000000000000000 : ℝ)=(100044124279059351473/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(7721242178435609/25000000000000000000 : ℝ) ≤ ((26181851683818766969/26190000000000000000 : ℝ)+2*(213627269491/130950000000000 : ℝ)*(353/2500 : ℝ))^(1057/256 : ℝ) := by
    rw [show (26181851683818766969/26190000000000000000 : ℝ)+2*(213627269491/130950000000000 : ℝ)*(353/2500 : ℝ)=(10001495743413371/10000000000000000 : ℝ) by norm_num, show 1+2*(7721242178435609/25000000000000000000 : ℝ)=(12507721242178435609/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (26181851683818766969/26190000000000000000 : ℝ)*(X 1 0+X 2 0)+(213627269491/130950000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1057/256 : ℝ)) (lo := (11501/100000 : ℝ)) (hi := (353/2500 : ℝ)) (c := (26181851683818766969/26190000000000000000 : ℝ)) (alpha := (213627269491/130950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (26181851683818766969/26190000000000000000 : ℝ)*(X 0 1+X 2 1)+(213627269491/130950000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1057/256 : ℝ)) (lo := (11501/100000 : ℝ)) (hi := (353/2500 : ℝ)) (c := (26181851683818766969/26190000000000000000 : ℝ)) (alpha := (213627269491/130950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (26181851683818766969/26190000000000000000 : ℝ)*(X 0 2+X 1 2)+(213627269491/130950000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1057/256 : ℝ)) (lo := (11501/100000 : ℝ)) (hi := (353/2500 : ℝ)) (c := (26181851683818766969/26190000000000000000 : ℝ)) (alpha := (213627269491/130950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2109874243/10000000000 : ℝ)*X 0 0+(5390779599/10000000000 : ℝ)*X 0 1+(5267509259/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1264_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344187957/10000000000 : ℝ)*X 1 0+(-54309259/250000000 : ℝ)*X 1 1+(329219329/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1264_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344187957/10000000000 : ℝ)*X 2 0+(526750927/1000000000 : ℝ)*X 2 1+(-135773147/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1264_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((86955301/200000000 : ℝ)*X 0 0+(2111978183/5000000000 : ℝ)*X 0 1+(2237540791/5000000000 : ℝ)*X 0 2+(86955301/200000000 : ℝ)*X 1 0+(2111978183/5000000000 : ℝ)*X 1 1+(2237540791/5000000000 : ℝ)*X 1 2+(86955301/200000000 : ℝ)*X 2 0+(2111978183/5000000000 : ℝ)*X 2 1+(2237540791/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1264_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2109879067/10000000000 : ℝ)*X 0 0+(526781987/1000000000 : ℝ)*X 0 1+(336904231/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1264_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((664086101/1250000000 : ℝ)*X 1 0+(-2049412147/10000000000 : ℝ)*X 1 1+(1078093443/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1264_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2656344431/5000000000 : ℝ)*X 2 0+(673808391/1250000000 : ℝ)*X 2 1+(-2049412191/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1264_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1086943613/2500000000 : ℝ)*X 0 0+(111861191/250000000 : ℝ)*X 0 1+(1056148149/2500000000 : ℝ)*X 0 2+(1086943613/2500000000 : ℝ)*X 1 0+(111861191/250000000 : ℝ)*X 1 1+(1056148149/2500000000 : ℝ)*X 1 2+(1086943613/2500000000 : ℝ)*X 2 0+(111861191/250000000 : ℝ)*X 2 1+(1056148149/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1264_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (168071065804086297234038117/72750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (96666561/20000000000000 : ℝ)*(base19) + (90289877/20000000000000 : ℝ)*(base23) + (170391/1000000000000 : ℝ)*(lower2) + (11188489/20000000000000 : ℝ)*(upper3) + (366513/800000000000 : ℝ)*(upper5) + (3023592725720279/50000000000000 : ℝ)*(major0) + (3023592725720279/50000000000000 : ℝ)*(major1) + (3023592725720279/50000000000000 : ℝ)*(major2) + (4056132899067043/50000000000000 : ℝ)*(sp0) + (8112279697750733/100000000000000 : ℝ)*(sp1) + (8112279729634153/100000000000000 : ℝ)*(sp2) + (199104185896159/5000000000000 : ℝ)*(sp3) + (14382949451/100000000000000 : ℝ)*(sp4) + (3463432943/50000000000000 : ℝ)*(sp7) + (1991045322394533/50000000000000 : ℝ)*(f.failure) + (4056140090541769/50000000000000 : ℝ)*(f.sum) + (16844770172959/13095000000000000000000000000 : ℝ)*base66 + (1886919008520511883/436500000000000000000000000000000 : ℝ)*base68 + (2470306575963511883/436500000000000000000000000000000 : ℝ)*base70 + (2741869798559011883/436500000000000000000000000000000 : ℝ)*base72 + (8655258024211/3273750000000000000000000000 : ℝ)*base74 + (19771690253488117/436500000000000000000000000000000 : ℝ)*base75 + (1975834013130988117/436500000000000000000000000000000 : ℝ)*base77 + (3797652111969511883/436500000000000000000000000000000 : ℝ)*base80 + (15772128362311/3273750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (5030921/5000000000000000000000 : ℝ)*base90 + (5030921/5000000000000000000000 : ℝ)*base92 + (5030921/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (214743472278172588017564659/109125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (399362781/25000000000000 : ℝ)*(base19) + (12125537/625000000000 : ℝ)*(base23) + (248987/160000000000 : ℝ)*(upper2) + (275839563/100000000000000 : ℝ)*(upper5) + (1519474034337989/25000000000000 : ℝ)*(major0) + (1519474034337989/25000000000000 : ℝ)*(major1) + (1519474034337989/25000000000000 : ℝ)*(major2) + (21182877753/100000000000000 : ℝ)*(sp0) + (24586835009/50000000000000 : ℝ)*(sp1) + (21790853589/50000000000000 : ℝ)*(sp2) + (4076728649075077/50000000000000 : ℝ)*(sp4) + (2038356927476691/25000000000000 : ℝ)*(sp5) + (8153432959234809/100000000000000 : ℝ)*(sp6) + (2001156864040217/50000000000000 : ℝ)*(sp7) + (2001156864040217/50000000000000 : ℝ)*(f.failure) + (4076739240513953/50000000000000 : ℝ)*(f.sum) + (67862543211953/13095000000000000000000000000 : ℝ)*base66 + (560899168868878447/218250000000000000000000000000000 : ℝ)*base67 + (322938992162878447/218250000000000000000000000000000 : ℝ)*base69 + (1248267522047128447/218250000000000000000000000000000 : ℝ)*base71 + (11803695837613/3273750000000000000000000000 : ℝ)*base73 + (736828183655371553/218250000000000000000000000000000 : ℝ)*base76 + (2783067985682371553/218250000000000000000000000000000 : ℝ)*base78 + (556473585942628447/218250000000000000000000000000000 : ℝ)*base79 + (94338757860337/13095000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (31954829/5000000000000000000000 : ℝ)*base90 + (31954829/5000000000000000000000 : ℝ)*base92 + (31954829/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1264_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1057/256 : ℝ) ≤ p) (hpb : p ≤ (8457/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151859563/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (353/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11501/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2301/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3529/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1264_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1264_s8_0 (p : ℝ) (hpa : (1057/256 : ℝ) ≤ p) (hpb : p ≤ (8457/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1068835769/2000000000 : ℝ)*x 0 + (5267544057/10000000000 : ℝ)*x 1 + (-2172336333/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1068835769/2000000000 : ℝ)^8457 ≤ (43744673547183/100000000000000 : ℝ)^6409 := by
    have hnat : (1068835769 : ℕ)^8457*100000000000000^6409 ≤ 43744673547183^6409*2000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068835769 2000000000 43744673547183 100000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5267544057/10000000000 : ℝ)^8457 ≤ (42918831912269/100000000000000 : ℝ)^6409 := by
    have hnat : (5267544057 : ℕ)^8457*100000000000000^6409 ≤ 42918831912269^6409*10000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267544057 10000000000 42918831912269 100000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2172336333/10000000000 : ℝ)^8457 ≤ (13336494521291/100000000000000 : ℝ)^6409 := by
    have hnat : (2172336333 : ℕ)^8457*100000000000000^6409 ≤ 13336494521291^6409*10000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2172336333 10000000000 13336494521291 100000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8457/2048 : ℝ)) 8457 6409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1068835769/2000000000 : ℝ), (5267544057/10000000000 : ℝ), (-2172336333/10000000000 : ℝ)] ![(43744673547183/100000000000000 : ℝ), (42918831912269/100000000000000 : ℝ), (13336494521291/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1068835769/2000000000 : ℝ)|^8457 ≤ (43744673547183/100000000000000 : ℝ)^6409
        have hw : |(1068835769/2000000000 : ℝ)|=(1068835769/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5267544057/10000000000 : ℝ)|^8457 ≤ (42918831912269/100000000000000 : ℝ)^6409
        have hw : |(5267544057/10000000000 : ℝ)|=(5267544057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2172336333/10000000000 : ℝ)|^8457 ≤ (13336494521291/100000000000000 : ℝ)^6409
        have hw : |(-2172336333/10000000000 : ℝ)|=(2172336333/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1264_s8_1 (p : ℝ) (hpa : (1057/256 : ℝ) ≤ p) (hpb : p ≤ (8457/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4347766837/10000000000 : ℝ)*x 0 + (4224028697/10000000000 : ℝ)*x 1 + (2237504401/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4347766837/10000000000 : ℝ)^8457 ≤ (6663524386633/20000000000000 : ℝ)^6409 := by
    have hnat : (4347766837 : ℕ)^8457*20000000000000^6409 ≤ 6663524386633^6409*10000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4347766837 10000000000 6663524386633 20000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4224028697/10000000000 : ℝ)^8457 ≤ (4009014754873/12500000000000 : ℝ)^6409 := by
    have hnat : (4224028697 : ℕ)^8457*12500000000000^6409 ≤ 4009014754873^6409*10000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4224028697 10000000000 4009014754873 12500000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2237504401/5000000000 : ℝ)^8457 ≤ (17305130006773/50000000000000 : ℝ)^6409 := by
    have hnat : (2237504401 : ℕ)^8457*50000000000000^6409 ≤ 17305130006773^6409*5000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2237504401 5000000000 17305130006773 50000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8457/2048 : ℝ)) 8457 6409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4347766837/10000000000 : ℝ), (4224028697/10000000000 : ℝ), (2237504401/5000000000 : ℝ)] ![(6663524386633/20000000000000 : ℝ), (4009014754873/12500000000000 : ℝ), (17305130006773/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4347766837/10000000000 : ℝ)|^8457 ≤ (6663524386633/20000000000000 : ℝ)^6409
        have hw : |(4347766837/10000000000 : ℝ)|=(4347766837/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4224028697/10000000000 : ℝ)|^8457 ≤ (4009014754873/12500000000000 : ℝ)^6409
        have hw : |(4224028697/10000000000 : ℝ)|=(4224028697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2237504401/5000000000 : ℝ)|^8457 ≤ (17305130006773/50000000000000 : ℝ)^6409
        have hw : |(2237504401/5000000000 : ℝ)|=(2237504401/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1264_s8_2 (p : ℝ) (hpa : (1057/256 : ℝ) ≤ p) (hpb : p ≤ (8457/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-527470251/2500000000 : ℝ)*x 0 + (5267855307/10000000000 : ℝ)*x 1 + (2695215541/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (527470251/2500000000 : ℝ)^8457 ≤ (6416440496309/50000000000000 : ℝ)^6409 := by
    have hnat : (527470251 : ℕ)^8457*50000000000000^6409 ≤ 6416440496309^6409*2500000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      527470251 2500000000 6416440496309 50000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5267855307/10000000000 : ℝ)^8457 ≤ (42922178322937/100000000000000 : ℝ)^6409 := by
    have hnat : (5267855307 : ℕ)^8457*100000000000000^6409 ≤ 42922178322937^6409*10000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267855307 10000000000 42922178322937 100000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2695215541/5000000000 : ℝ)^8457 ≤ (4424494066171/10000000000000 : ℝ)^6409 := by
    have hnat : (2695215541 : ℕ)^8457*10000000000000^6409 ≤ 4424494066171^6409*5000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695215541 5000000000 4424494066171 10000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8457/2048 : ℝ)) 8457 6409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-527470251/2500000000 : ℝ), (5267855307/10000000000 : ℝ), (2695215541/5000000000 : ℝ)] ![(6416440496309/50000000000000 : ℝ), (42922178322937/100000000000000 : ℝ), (4424494066171/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-527470251/2500000000 : ℝ)|^8457 ≤ (6416440496309/50000000000000 : ℝ)^6409
        have hw : |(-527470251/2500000000 : ℝ)|=(527470251/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5267855307/10000000000 : ℝ)|^8457 ≤ (42922178322937/100000000000000 : ℝ)^6409
        have hw : |(5267855307/10000000000 : ℝ)|=(5267855307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2695215541/5000000000 : ℝ)|^8457 ≤ (4424494066171/10000000000000 : ℝ)^6409
        have hw : |(2695215541/5000000000 : ℝ)|=(2695215541/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1264_s8_3 (p : ℝ) (hpa : (1057/256 : ℝ) ≤ p) (hpb : p ≤ (8457/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2656348649/5000000000 : ℝ)*x 0 + (-204944923/1000000000 : ℝ)*x 1 + (5390431539/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656348649/5000000000 : ℝ)^8457 ≤ (43404956907517/100000000000000 : ℝ)^6409 := by
    have hnat : (2656348649 : ℕ)^8457*100000000000000^6409 ≤ 43404956907517^6409*5000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656348649 5000000000 43404956907517 100000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (204944923/1000000000 : ℝ)^8457 ≤ (192970272919/1562500000000 : ℝ)^6409 := by
    have hnat : (204944923 : ℕ)^8457*1562500000000^6409 ≤ 192970272919^6409*1000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      204944923 1000000000 192970272919 1562500000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5390431539/10000000000 : ℝ)^8457 ≤ (884898912229/2000000000000 : ℝ)^6409 := by
    have hnat : (5390431539 : ℕ)^8457*2000000000000^6409 ≤ 884898912229^6409*10000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390431539 10000000000 884898912229 2000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8457/2048 : ℝ)) 8457 6409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656348649/5000000000 : ℝ), (-204944923/1000000000 : ℝ), (5390431539/10000000000 : ℝ)] ![(43404956907517/100000000000000 : ℝ), (192970272919/1562500000000 : ℝ), (884898912229/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656348649/5000000000 : ℝ)|^8457 ≤ (43404956907517/100000000000000 : ℝ)^6409
        have hw : |(2656348649/5000000000 : ℝ)|=(2656348649/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-204944923/1000000000 : ℝ)|^8457 ≤ (192970272919/1562500000000 : ℝ)^6409
        have hw : |(-204944923/1000000000 : ℝ)|=(204944923/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5390431539/10000000000 : ℝ)|^8457 ≤ (884898912229/2000000000000 : ℝ)^6409
        have hw : |(5390431539/10000000000 : ℝ)|=(5390431539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1264_s8_4 (p : ℝ) (hpa : (1057/256 : ℝ) ≤ p) (hpb : p ≤ (8457/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (166021791/312500000 : ℝ)*x 0 + (673803957/1250000000 : ℝ)*x 1 + (-512362263/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (166021791/312500000 : ℝ)^8457 ≤ (2712809816153/6250000000000 : ℝ)^6409 := by
    have hnat : (166021791 : ℕ)^8457*6250000000000^6409 ≤ 2712809816153^6409*312500000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      166021791 312500000 2712809816153 6250000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (673803957/1250000000 : ℝ)^8457 ≤ (4424494687867/10000000000000 : ℝ)^6409 := by
    have hnat : (673803957 : ℕ)^8457*10000000000000^6409 ≤ 4424494687867^6409*1250000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      673803957 1250000000 4424494687867 10000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (512362263/2500000000 : ℝ)^8457 ≤ (1543762006427/12500000000000 : ℝ)^6409 := by
    have hnat : (512362263 : ℕ)^8457*12500000000000^6409 ≤ 1543762006427^6409*2500000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      512362263 2500000000 1543762006427 12500000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8457/2048 : ℝ)) 8457 6409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(166021791/312500000 : ℝ), (673803957/1250000000 : ℝ), (-512362263/2500000000 : ℝ)] ![(2712809816153/6250000000000 : ℝ), (4424494687867/10000000000000 : ℝ), (1543762006427/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(166021791/312500000 : ℝ)|^8457 ≤ (2712809816153/6250000000000 : ℝ)^6409
        have hw : |(166021791/312500000 : ℝ)|=(166021791/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(673803957/1250000000 : ℝ)|^8457 ≤ (4424494687867/10000000000000 : ℝ)^6409
        have hw : |(673803957/1250000000 : ℝ)|=(673803957/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-512362263/2500000000 : ℝ)|^8457 ≤ (1543762006427/12500000000000 : ℝ)^6409
        have hw : |(-512362263/2500000000 : ℝ)|=(512362263/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1264_s8_5 (p : ℝ) (hpa : (1057/256 : ℝ) ≤ p) (hpb : p ≤ (8457/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4347776151/10000000000 : ℝ)*x 0 + (4474375819/10000000000 : ℝ)*x 1 + (2112332017/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4347776151/10000000000 : ℝ)^8457 ≤ (1665885805783/5000000000000 : ℝ)^6409 := by
    have hnat : (4347776151 : ℕ)^8457*5000000000000^6409 ≤ 1665885805783^6409*10000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4347776151 10000000000 1665885805783 5000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4474375819/10000000000 : ℝ)^8457 ≤ (34603800210781/100000000000000 : ℝ)^6409 := by
    have hnat : (4474375819 : ℕ)^8457*100000000000000^6409 ≤ 34603800210781^6409*10000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4474375819 10000000000 34603800210781 100000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2112332017/5000000000 : ℝ)^8457 ≤ (32078483669471/100000000000000 : ℝ)^6409 := by
    have hnat : (2112332017 : ℕ)^8457*100000000000000^6409 ≤ 32078483669471^6409*5000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2112332017 5000000000 32078483669471 100000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8457/2048 : ℝ)) 8457 6409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4347776151/10000000000 : ℝ), (4474375819/10000000000 : ℝ), (2112332017/5000000000 : ℝ)] ![(1665885805783/5000000000000 : ℝ), (34603800210781/100000000000000 : ℝ), (32078483669471/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4347776151/10000000000 : ℝ)|^8457 ≤ (1665885805783/5000000000000 : ℝ)^6409
        have hw : |(4347776151/10000000000 : ℝ)|=(4347776151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4474375819/10000000000 : ℝ)|^8457 ≤ (34603800210781/100000000000000 : ℝ)^6409
        have hw : |(4474375819/10000000000 : ℝ)|=(4474375819/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2112332017/5000000000 : ℝ)|^8457 ≤ (32078483669471/100000000000000 : ℝ)^6409
        have hw : |(2112332017/5000000000 : ℝ)|=(2112332017/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1264_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1057/256 : ℝ) ≤ p) (hpb : p ≤ (8457/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151859563/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3529/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2301/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (2301/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2823/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3529/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2301/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3529/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2301/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3529/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2301/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3529/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2301/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3529/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2301/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3529/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2301/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base8 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 0).1]
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
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
  have hpowlo : (2301/20000 : ℝ) ^ (1057/256 : ℝ) ≤ (265166651198753/2000000000000000000 : ℝ) := by
    have hpowers : (2301/20000 : ℝ)^1057 ≤ (265166651198753/2000000000000000000 : ℝ)^256 := by
      have hnat : (2301 : ℕ)^1057*2000000000000000000^256 ≤ 265166651198753^256*20000^1057 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2301 20000 265166651198753 2000000000000000000 1057 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2301/20000 : ℝ)) (X := (265166651198753/2000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1057 256 (by norm_num) hpowers
    exact h
  have hpowhi : (3529/25000 : ℝ) ^ (1057/256 : ℝ) ≤ (30848859751733049/100000000000000000000 : ℝ) := by
    have hpowers : (3529/25000 : ℝ)^1057 ≤ (30848859751733049/100000000000000000000 : ℝ)^256 := by
      have hnat : (3529 : ℕ)^1057*100000000000000000000^256 ≤ 30848859751733049^256*25000^1057 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3529 25000 30848859751733049 100000000000000000000 1057 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3529/25000 : ℝ)) (X := (30848859751733049/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1057 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (1000265166651198753/1000000000000000000 : ℝ) ≤ (2000128431113411/2000000000000000 : ℝ) ^ (1057/256 : ℝ) := by
    have hpowers : (1000265166651198753/1000000000000000000 : ℝ)^256 ≤ (2000128431113411/2000000000000000 : ℝ)^1057 := by
      have hnat : (1000265166651198753 : ℕ)^256*2000000000000000^1057 ≤ 2000128431113411^1057*1000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1000265166651198753 1000000000000000000 2000128431113411 2000000000000000 256 1057 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000128431113411/2000000000000000 : ℝ)) (X := (1000265166651198753/1000000000000000000 : ℝ)) (by norm_num) 1057 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (100044107192311670699/100000000000000000000 : ℝ) ≤ (312533377349387/312500000000000 : ℝ) ^ (1057/256 : ℝ) := by
    have hpowers : (100044107192311670699/100000000000000000000 : ℝ)^256 ≤ (312533377349387/312500000000000 : ℝ)^1057 := by
      have hnat : (100044107192311670699 : ℕ)^256*312500000000000^1057 ≤ 312533377349387^1057*100000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100044107192311670699 100000000000000000000 312533377349387 312500000000000 256 1057 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312533377349387/312500000000000 : ℝ)) (X := (100044107192311670699/100000000000000000000 : ℝ)) (by norm_num) 1057 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (50030848859751733049/50000000000000000000 : ℝ) ≤ (10001493994793713/10000000000000000 : ℝ) ^ (1057/256 : ℝ) := by
    have hpowers : (50030848859751733049/50000000000000000000 : ℝ)^256 ≤ (10001493994793713/10000000000000000 : ℝ)^1057 := by
      have hnat : (50030848859751733049 : ℕ)^256*10000000000000000^1057 ≤ 10001493994793713^1057*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50030848859751733049 50000000000000000000 10001493994793713 10000000000000000 256 1057 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001493994793713/10000000000000000 : ℝ)) (X := (50030848859751733049/50000000000000000000 : ℝ)) (by norm_num) 1057 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(265166651198753/2000000000000000000 : ℝ) ≤ ((745767893082368009/746000000000000000 : ℝ)+2*(60845659047/37300000000000 : ℝ)*(2301/20000 : ℝ))^(1057/256 : ℝ) := by
    rw [show (745767893082368009/746000000000000000 : ℝ)+2*(60845659047/37300000000000 : ℝ)*(2301/20000 : ℝ)=(2000128431113411/2000000000000000 : ℝ) by norm_num, show 1+2*(265166651198753/2000000000000000000 : ℝ)=(1000265166651198753/1000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(30848859751733049/100000000000000000000 : ℝ)+(265166651198753/2000000000000000000 : ℝ) ≤ ((745767893082368009/746000000000000000 : ℝ)+(60845659047/37300000000000 : ℝ)*((3529/25000 : ℝ)+(2301/20000 : ℝ)))^(1057/256 : ℝ) := by
    rw [show (745767893082368009/746000000000000000 : ℝ)+(60845659047/37300000000000 : ℝ)*((3529/25000 : ℝ)+(2301/20000 : ℝ))=(312533377349387/312500000000000 : ℝ) by norm_num, show 1+(30848859751733049/100000000000000000000 : ℝ)+(265166651198753/2000000000000000000 : ℝ)=(100044107192311670699/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(30848859751733049/100000000000000000000 : ℝ) ≤ ((745767893082368009/746000000000000000 : ℝ)+2*(60845659047/37300000000000 : ℝ)*(3529/25000 : ℝ))^(1057/256 : ℝ) := by
    rw [show (745767893082368009/746000000000000000 : ℝ)+2*(60845659047/37300000000000 : ℝ)*(3529/25000 : ℝ)=(10001493994793713/10000000000000000 : ℝ) by norm_num, show 1+2*(30848859751733049/100000000000000000000 : ℝ)=(50030848859751733049/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (745767893082368009/746000000000000000 : ℝ)*(X 1 0+X 2 0)+(60845659047/37300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1057/256 : ℝ)) (lo := (2301/20000 : ℝ)) (hi := (3529/25000 : ℝ)) (c := (745767893082368009/746000000000000000 : ℝ)) (alpha := (60845659047/37300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (745767893082368009/746000000000000000 : ℝ)*(X 0 1+X 2 1)+(60845659047/37300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1057/256 : ℝ)) (lo := (2301/20000 : ℝ)) (hi := (3529/25000 : ℝ)) (c := (745767893082368009/746000000000000000 : ℝ)) (alpha := (60845659047/37300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (745767893082368009/746000000000000000 : ℝ)*(X 0 2+X 1 2)+(60845659047/37300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1057/256 : ℝ)) (lo := (2301/20000 : ℝ)) (hi := (3529/25000 : ℝ)) (c := (745767893082368009/746000000000000000 : ℝ)) (alpha := (60845659047/37300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((1068835769/2000000000 : ℝ)*X 2 0+(5267544057/10000000000 : ℝ)*X 2 1+(-2172336333/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1264_s8_0 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((4347766837/10000000000 : ℝ)*X 0 0+(4224028697/10000000000 : ℝ)*X 0 1+(2237504401/5000000000 : ℝ)*X 0 2+(4347766837/10000000000 : ℝ)*X 1 0+(4224028697/10000000000 : ℝ)*X 1 1+(2237504401/5000000000 : ℝ)*X 1 2+(4347766837/10000000000 : ℝ)*X 2 0+(4224028697/10000000000 : ℝ)*X 2 1+(2237504401/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1264_s8_1 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((-527470251/2500000000 : ℝ)*X 0 0+(5267855307/10000000000 : ℝ)*X 0 1+(2695215541/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1264_s8_2 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2656348649/5000000000 : ℝ)*X 1 0+(-204944923/1000000000 : ℝ)*X 1 1+(5390431539/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1264_s8_3 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((166021791/312500000 : ℝ)*X 2 0+(673803957/1250000000 : ℝ)*X 2 1+(-512362263/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1264_s8_4 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((4347776151/10000000000 : ℝ)*X 0 0+(4474375819/10000000000 : ℝ)*X 0 1+(2112332017/5000000000 : ℝ)*X 0 2+(4347776151/10000000000 : ℝ)*X 1 0+(4474375819/10000000000 : ℝ)*X 1 1+(2112332017/5000000000 : ℝ)*X 1 2+(4347776151/10000000000 : ℝ)*X 2 0+(4474375819/10000000000 : ℝ)*X 2 1+(2112332017/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1264_s8_5 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(lower0) + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (497100724490259027663/186500000000000000000000000 : ℝ) := by norm_num
    linear_combination (10403361/10000000000000 : ℝ)*(base8) + (795683781/100000000000000 : ℝ)*(base15) + (15478741/100000000000000 : ℝ)*(upper2) + (13622319/5000000000000 : ℝ)*(lower4) + (14369691/12500000000000 : ℝ)*(lower5) + (243256339221543/4000000000000 : ℝ)*(major0) + (243256339221543/4000000000000 : ℝ)*(major1) + (243256339221543/4000000000000 : ℝ)*(major2) + (730730809/3125000000000 : ℝ)*(sp0) + (272330677/3125000000000 : ℝ)*(sp1) + (8158190151077233/100000000000000 : ℝ)*(sp2) + (4079094729713531/50000000000000 : ℝ)*(sp3) + (4079083435862477/50000000000000 : ℝ)*(sp4) + (2002308951268661/50000000000000 : ℝ)*(sp5) + (2002313308559493/50000000000000 : ℝ)*(f.failure) + (8158190255110843/100000000000000 : ℝ)*(f.sum) + (1689206369229/373000000000000000000000000 : ℝ)*base66 + (2842260608850113/2984000000000000000000000000000 : ℝ)*base68 + (8420890584549887/2984000000000000000000000000000 : ℝ)*base69 + (76677786094906113/2984000000000000000000000000000 : ℝ)*base72 + (2035299569613/373000000000000000000000000 : ℝ)*base74 + (1513299914458113/2984000000000000000000000000000 : ℝ)*base76 + (24405856861605887/2984000000000000000000000000000 : ℝ)*base77 + (7264887838693887/2984000000000000000000000000000 : ℝ)*base79 + (511841003433/373000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (16481559/5000000000000000000000 : ℝ)*base89 + (16481559/5000000000000000000000 : ℝ)*base91 + (16481559/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1264_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1057/256 : ℝ) ≤ p) (hpb : p ≤ (8457/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151859563/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3529/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2301/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2301/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2823/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1264_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1264_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1057/256 : ℝ) ≤ p) (hpb : p ≤ (8457/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151859563/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14139/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5741/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2301/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2823/20000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1264_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1264_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1264_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (1057/256 : ℝ) ≤ p) (hpb : p ≤ (8457/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151859563/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14139/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5741/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2301/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2823/20000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1264_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
