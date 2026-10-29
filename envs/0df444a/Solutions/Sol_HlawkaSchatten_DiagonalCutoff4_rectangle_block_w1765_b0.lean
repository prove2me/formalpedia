-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1765_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:29:45.765572+00:00
-- url     : https://prove2.me/submissions/09321ff5-fecd-4ce8-a37d-891fcc1ec827

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
theorem support_rectangle_w1765_s0_0 (p : ℝ) (hpa : (5999/1024 : ℝ) ≤ p) (hpb : p ≤ (6015/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-554400799/5000000000 : ℝ)*x 0 + (2793542331/5000000000 : ℝ)*x 1 + (624830187/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (554400799/5000000000 : ℝ)^6015 ≤ (882667595891/12500000000000 : ℝ)^4991 := by
    have hnat : (554400799 : ℕ)^6015*12500000000000^4991 ≤ 882667595891^4991*5000000000^6015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      554400799 5000000000 882667595891 12500000000000 6015 4991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2793542331/5000000000 : ℝ)^6015 ≤ (49581016499679/100000000000000 : ℝ)^4991 := by
    have hnat : (2793542331 : ℕ)^6015*100000000000000^4991 ≤ 49581016499679^4991*5000000000^6015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2793542331 5000000000 49581016499679 100000000000000 6015 4991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (624830187/1250000000 : ℝ)^6015 ≤ (43357642720367/100000000000000 : ℝ)^4991 := by
    have hnat : (624830187 : ℕ)^6015*100000000000000^4991 ≤ 43357642720367^4991*1250000000^6015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      624830187 1250000000 43357642720367 100000000000000 6015 4991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6015/1024 : ℝ)) 6015 4991 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-554400799/5000000000 : ℝ), (2793542331/5000000000 : ℝ), (624830187/1250000000 : ℝ)] ![(882667595891/12500000000000 : ℝ), (49581016499679/100000000000000 : ℝ), (43357642720367/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-554400799/5000000000 : ℝ)|^6015 ≤ (882667595891/12500000000000 : ℝ)^4991
        have hw : |(-554400799/5000000000 : ℝ)|=(554400799/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2793542331/5000000000 : ℝ)|^6015 ≤ (49581016499679/100000000000000 : ℝ)^4991
        have hw : |(2793542331/5000000000 : ℝ)|=(2793542331/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(624830187/1250000000 : ℝ)|^6015 ≤ (43357642720367/100000000000000 : ℝ)^4991
        have hw : |(624830187/1250000000 : ℝ)|=(624830187/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1765_s0_1 (p : ℝ) (hpa : (5999/1024 : ℝ) ≤ p) (hpb : p ≤ (6015/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2677493089/5000000000 : ℝ)*x 0 + (-711170747/5000000000 : ℝ)*x 1 + (4998641041/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2677493089/5000000000 : ℝ)^6015 ≤ (11777358714189/25000000000000 : ℝ)^4991 := by
    have hnat : (2677493089 : ℕ)^6015*25000000000000^4991 ≤ 11777358714189^4991*5000000000^6015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2677493089 5000000000 11777358714189 25000000000000 6015 4991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (711170747/5000000000 : ℝ)^6015 ≤ (2383231790993/25000000000000 : ℝ)^4991 := by
    have hnat : (711170747 : ℕ)^6015*25000000000000^4991 ≤ 2383231790993^4991*5000000000^6015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      711170747 5000000000 2383231790993 25000000000000 6015 4991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4998641041/10000000000 : ℝ)^6015 ≤ (1734305518561/4000000000000 : ℝ)^4991 := by
    have hnat : (4998641041 : ℕ)^6015*4000000000000^4991 ≤ 1734305518561^4991*10000000000^6015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4998641041 10000000000 1734305518561 4000000000000 6015 4991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6015/1024 : ℝ)) 6015 4991 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2677493089/5000000000 : ℝ), (-711170747/5000000000 : ℝ), (4998641041/10000000000 : ℝ)] ![(11777358714189/25000000000000 : ℝ), (2383231790993/25000000000000 : ℝ), (1734305518561/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2677493089/5000000000 : ℝ)|^6015 ≤ (11777358714189/25000000000000 : ℝ)^4991
        have hw : |(2677493089/5000000000 : ℝ)|=(2677493089/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-711170747/5000000000 : ℝ)|^6015 ≤ (2383231790993/25000000000000 : ℝ)^4991
        have hw : |(-711170747/5000000000 : ℝ)|=(711170747/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4998641041/10000000000 : ℝ)|^6015 ≤ (1734305518561/4000000000000 : ℝ)^4991
        have hw : |(4998641041/10000000000 : ℝ)|=(4998641041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1765_s0_2 (p : ℝ) (hpa : (5999/1024 : ℝ) ≤ p) (hpb : p ≤ (6015/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5354983041/10000000000 : ℝ)*x 0 + (2499321551/5000000000 : ℝ)*x 1 + (-44448217/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5354983041/10000000000 : ℝ)^6015 ≤ (47109401597533/100000000000000 : ℝ)^4991 := by
    have hnat : (5354983041 : ℕ)^6015*100000000000000^4991 ≤ 47109401597533^4991*10000000000^6015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5354983041 10000000000 47109401597533 100000000000000 6015 4991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2499321551/5000000000 : ℝ)^6015 ≤ (43357659508689/100000000000000 : ℝ)^4991 := by
    have hnat : (2499321551 : ℕ)^6015*100000000000000^4991 ≤ 43357659508689^4991*5000000000^6015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2499321551 5000000000 43357659508689 100000000000000 6015 4991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (44448217/312500000 : ℝ)^6015 ≤ (9532938876173/100000000000000 : ℝ)^4991 := by
    have hnat : (44448217 : ℕ)^6015*100000000000000^4991 ≤ 9532938876173^4991*312500000^6015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      44448217 312500000 9532938876173 100000000000000 6015 4991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6015/1024 : ℝ)) 6015 4991 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5354983041/10000000000 : ℝ), (2499321551/5000000000 : ℝ), (-44448217/312500000 : ℝ)] ![(47109401597533/100000000000000 : ℝ), (43357659508689/100000000000000 : ℝ), (9532938876173/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5354983041/10000000000 : ℝ)|^6015 ≤ (47109401597533/100000000000000 : ℝ)^4991
        have hw : |(5354983041/10000000000 : ℝ)|=(5354983041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2499321551/5000000000 : ℝ)|^6015 ≤ (43357659508689/100000000000000 : ℝ)^4991
        have hw : |(2499321551/5000000000 : ℝ)|=(2499321551/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-44448217/312500000 : ℝ)|^6015 ≤ (9532938876173/100000000000000 : ℝ)^4991
        have hw : |(-44448217/312500000 : ℝ)|=(44448217/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1765_s0_3 (p : ℝ) (hpa : (5999/1024 : ℝ) ≤ p) (hpb : p ≤ (6015/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (988971509/2500000000 : ℝ)*x 0 + (2997209989/10000000000 : ℝ)*x 1 + (5049299039/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (988971509/2500000000 : ℝ)^6015 ≤ (32704729111319/100000000000000 : ℝ)^4991 := by
    have hnat : (988971509 : ℕ)^6015*100000000000000^4991 ≤ 32704729111319^4991*2500000000^6015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      988971509 2500000000 32704729111319 100000000000000 6015 4991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2997209989/10000000000 : ℝ)^6015 ≤ (2925941307397/12500000000000 : ℝ)^4991 := by
    have hnat : (2997209989 : ℕ)^6015*12500000000000^4991 ≤ 2925941307397^4991*10000000000^6015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2997209989 10000000000 2925941307397 12500000000000 6015 4991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5049299039/10000000000 : ℝ)^6015 ≤ (10971935104141/25000000000000 : ℝ)^4991 := by
    have hnat : (5049299039 : ℕ)^6015*25000000000000^4991 ≤ 10971935104141^4991*10000000000^6015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5049299039 10000000000 10971935104141 25000000000000 6015 4991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6015/1024 : ℝ)) 6015 4991 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(988971509/2500000000 : ℝ), (2997209989/10000000000 : ℝ), (5049299039/10000000000 : ℝ)] ![(32704729111319/100000000000000 : ℝ), (2925941307397/12500000000000 : ℝ), (10971935104141/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(988971509/2500000000 : ℝ)|^6015 ≤ (32704729111319/100000000000000 : ℝ)^4991
        have hw : |(988971509/2500000000 : ℝ)|=(988971509/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2997209989/10000000000 : ℝ)|^6015 ≤ (2925941307397/12500000000000 : ℝ)^4991
        have hw : |(2997209989/10000000000 : ℝ)|=(2997209989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5049299039/10000000000 : ℝ)|^6015 ≤ (10971935104141/25000000000000 : ℝ)^4991
        have hw : |(5049299039/10000000000 : ℝ)|=(5049299039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1765_s0_4 (p : ℝ) (hpa : (5999/1024 : ℝ) ≤ p) (hpb : p ≤ (6015/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-55494451/500000000 : ℝ)*x 0 + (5013283287/10000000000 : ℝ)*x 1 + (5571984471/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (55494451/500000000 : ℝ)^6015 ≤ (883710953521/12500000000000 : ℝ)^4991 := by
    have hnat : (55494451 : ℕ)^6015*12500000000000^4991 ≤ 883710953521^4991*500000000^6015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      55494451 500000000 883710953521 12500000000000 6015 4991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5013283287/10000000000 : ℝ)^6015 ≤ (43510746642429/100000000000000 : ℝ)^4991 := by
    have hnat : (5013283287 : ℕ)^6015*100000000000000^4991 ≤ 43510746642429^4991*10000000000^6015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5013283287 10000000000 43510746642429 100000000000000 6015 4991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5571984471/10000000000 : ℝ)^6015 ≤ (49419565713909/100000000000000 : ℝ)^4991 := by
    have hnat : (5571984471 : ℕ)^6015*100000000000000^4991 ≤ 49419565713909^4991*10000000000^6015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5571984471 10000000000 49419565713909 100000000000000 6015 4991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6015/1024 : ℝ)) 6015 4991 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-55494451/500000000 : ℝ), (5013283287/10000000000 : ℝ), (5571984471/10000000000 : ℝ)] ![(883710953521/12500000000000 : ℝ), (43510746642429/100000000000000 : ℝ), (49419565713909/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-55494451/500000000 : ℝ)|^6015 ≤ (883710953521/12500000000000 : ℝ)^4991
        have hw : |(-55494451/500000000 : ℝ)|=(55494451/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5013283287/10000000000 : ℝ)|^6015 ≤ (43510746642429/100000000000000 : ℝ)^4991
        have hw : |(5013283287/10000000000 : ℝ)|=(5013283287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5571984471/10000000000 : ℝ)|^6015 ≤ (49419565713909/100000000000000 : ℝ)^4991
        have hw : |(5571984471/10000000000 : ℝ)|=(5571984471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1765_s0_5 (p : ℝ) (hpa : (5999/1024 : ℝ) ≤ p) (hpb : p ≤ (6015/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1299778649/2500000000 : ℝ)*x 0 + (-424499969/5000000000 : ℝ)*x 1 + (1114396893/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1299778649/2500000000 : ℝ)^6015 ≤ (2841363765453/6250000000000 : ℝ)^4991 := by
    have hnat : (1299778649 : ℕ)^6015*6250000000000^4991 ≤ 2841363765453^4991*2500000000^6015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1299778649 2500000000 2841363765453 6250000000000 6015 4991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (424499969/5000000000 : ℝ)^6015 ≤ (5118614086281/100000000000000 : ℝ)^4991 := by
    have hnat : (424499969 : ℕ)^6015*100000000000000^4991 ≤ 5118614086281^4991*5000000000^6015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      424499969 5000000000 5118614086281 100000000000000 6015 4991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1114396893/2000000000 : ℝ)^6015 ≤ (1976782625991/4000000000000 : ℝ)^4991 := by
    have hnat : (1114396893 : ℕ)^6015*4000000000000^4991 ≤ 1976782625991^4991*2000000000^6015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1114396893 2000000000 1976782625991 4000000000000 6015 4991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6015/1024 : ℝ)) 6015 4991 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1299778649/2500000000 : ℝ), (-424499969/5000000000 : ℝ), (1114396893/2000000000 : ℝ)] ![(2841363765453/6250000000000 : ℝ), (5118614086281/100000000000000 : ℝ), (1976782625991/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1299778649/2500000000 : ℝ)|^6015 ≤ (2841363765453/6250000000000 : ℝ)^4991
        have hw : |(1299778649/2500000000 : ℝ)|=(1299778649/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-424499969/5000000000 : ℝ)|^6015 ≤ (5118614086281/100000000000000 : ℝ)^4991
        have hw : |(-424499969/5000000000 : ℝ)|=(424499969/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1114396893/2000000000 : ℝ)|^6015 ≤ (1976782625991/4000000000000 : ℝ)^4991
        have hw : |(1114396893/2000000000 : ℝ)|=(1114396893/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1765_s0_6 (p : ℝ) (hpa : (5999/1024 : ℝ) ≤ p) (hpb : p ≤ (6015/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1299778717/2500000000 : ℝ)*x 0 + (5571984441/10000000000 : ℝ)*x 1 + (-848999579/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1299778717/2500000000 : ℝ)^6015 ≤ (1420681972301/3125000000000 : ℝ)^4991 := by
    have hnat : (1299778717 : ℕ)^6015*3125000000000^4991 ≤ 1420681972301^4991*2500000000^6015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1299778717 2500000000 1420681972301 3125000000000 6015 4991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5571984441/10000000000 : ℝ)^6015 ≤ (49419565393239/100000000000000 : ℝ)^4991 := by
    have hnat : (5571984441 : ℕ)^6015*100000000000000^4991 ≤ 49419565393239^4991*10000000000^6015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5571984441 10000000000 49419565393239 100000000000000 6015 4991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (848999579/10000000000 : ℝ)^6015 ≤ (5118611477803/100000000000000 : ℝ)^4991 := by
    have hnat : (848999579 : ℕ)^6015*100000000000000^4991 ≤ 5118611477803^4991*10000000000^6015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      848999579 10000000000 5118611477803 100000000000000 6015 4991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6015/1024 : ℝ)) 6015 4991 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1299778717/2500000000 : ℝ), (5571984441/10000000000 : ℝ), (-848999579/10000000000 : ℝ)] ![(1420681972301/3125000000000 : ℝ), (49419565393239/100000000000000 : ℝ), (5118611477803/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1299778717/2500000000 : ℝ)|^6015 ≤ (1420681972301/3125000000000 : ℝ)^4991
        have hw : |(1299778717/2500000000 : ℝ)|=(1299778717/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5571984441/10000000000 : ℝ)|^6015 ≤ (49419565393239/100000000000000 : ℝ)^4991
        have hw : |(5571984441/10000000000 : ℝ)|=(5571984441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-848999579/10000000000 : ℝ)|^6015 ≤ (5118611477803/100000000000000 : ℝ)^4991
        have hw : |(-848999579/10000000000 : ℝ)|=(848999579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1765_s0_7 (p : ℝ) (hpa : (5999/1024 : ℝ) ≤ p) (hpb : p ≤ (6015/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (494959421/1250000000 : ℝ)*x 0 + (1249560459/2500000000 : ℝ)*x 1 + (3049868527/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (494959421/1250000000 : ℝ)^6015 ≤ (8185622020941/25000000000000 : ℝ)^4991 := by
    have hnat : (494959421 : ℕ)^6015*25000000000000^4991 ≤ 8185622020941^4991*1250000000^6015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      494959421 1250000000 8185622020941 25000000000000 6015 4991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1249560459/2500000000 : ℝ)^6015 ≤ (1734138596349/4000000000000 : ℝ)^4991 := by
    have hnat : (1249560459 : ℕ)^6015*4000000000000^4991 ≤ 1734138596349^4991*2500000000^6015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1249560459 2500000000 1734138596349 4000000000000 6015 4991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3049868527/10000000000 : ℝ)^6015 ≤ (1494002936943/6250000000000 : ℝ)^4991 := by
    have hnat : (3049868527 : ℕ)^6015*6250000000000^4991 ≤ 1494002936943^4991*10000000000^6015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3049868527 10000000000 1494002936943 6250000000000 6015 4991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6015/1024 : ℝ)) 6015 4991 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(494959421/1250000000 : ℝ), (1249560459/2500000000 : ℝ), (3049868527/10000000000 : ℝ)] ![(8185622020941/25000000000000 : ℝ), (1734138596349/4000000000000 : ℝ), (1494002936943/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(494959421/1250000000 : ℝ)|^6015 ≤ (8185622020941/25000000000000 : ℝ)^4991
        have hw : |(494959421/1250000000 : ℝ)|=(494959421/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1249560459/2500000000 : ℝ)|^6015 ≤ (1734138596349/4000000000000 : ℝ)^4991
        have hw : |(1249560459/2500000000 : ℝ)|=(1249560459/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3049868527/10000000000 : ℝ)|^6015 ≤ (1494002936943/6250000000000 : ℝ)^4991
        have hw : |(3049868527/10000000000 : ℝ)|=(3049868527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1765_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5999/1024 : ℝ) ≤ p) (hpb : p ≤ (6015/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (56091581/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (7273/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (5011/25000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (5999/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^5999 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^5999*1^1024 ≤ 0^1024*1^5999 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 5999 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 5999 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (5999/1024 : ℝ) ≤ (116586666156365927/25000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^5999 ≤ (116586666156365927/25000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^5999*25000000000000000000^1024 ≤ 116586666156365927^1024*5^5999 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 116586666156365927 25000000000000000000 5999 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (116586666156365927/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5999 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (5999/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^5999 := by
      have hnat : (1 : ℕ)^1024*1^5999 ≤ 1^5999*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 5999 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 5999 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25116586666156365927/25000000000000000000 : ℝ) ≤ (10007944960429733/10000000000000000 : ℝ) ^ (5999/1024 : ℝ) := by
    have hpowers : (25116586666156365927/25000000000000000000 : ℝ)^1024 ≤ (10007944960429733/10000000000000000 : ℝ)^5999 := by
      have hnat : (25116586666156365927 : ℕ)^1024*10000000000000000^5999 ≤ 10007944960429733^5999*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25116586666156365927 25000000000000000000 10007944960429733 10000000000000000 1024 5999 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10007944960429733/10000000000000000 : ℝ)) (X := (25116586666156365927/25000000000000000000 : ℝ)) (by norm_num) 5999 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12616586666156365927/12500000000000000000 : ℝ) ≤ (5007944960429733/5000000000000000 : ℝ) ^ (5999/1024 : ℝ) := by
    have hpowers : (12616586666156365927/12500000000000000000 : ℝ)^1024 ≤ (5007944960429733/5000000000000000 : ℝ)^5999 := by
      have hnat : (12616586666156365927 : ℕ)^1024*5000000000000000^5999 ≤ 5007944960429733^5999*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12616586666156365927 12500000000000000000 5007944960429733 5000000000000000 1024 5999 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5007944960429733/5000000000000000 : ℝ)) (X := (12616586666156365927/12500000000000000000 : ℝ)) (by norm_num) 5999 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(7944960429733/4000000000000000 : ℝ)*(0 : ℝ))^(5999/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(7944960429733/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(116586666156365927/25000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(7944960429733/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(5999/1024 : ℝ) := by
    rw [show (1 : ℝ)+(7944960429733/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10007944960429733/10000000000000000 : ℝ) by norm_num, show 1+(116586666156365927/25000000000000000000 : ℝ)+(0 : ℝ)=(25116586666156365927/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(116586666156365927/25000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(7944960429733/4000000000000000 : ℝ)*(2/5 : ℝ))^(5999/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(7944960429733/4000000000000000 : ℝ)*(2/5 : ℝ)=(5007944960429733/5000000000000000 : ℝ) by norm_num, show 1+2*(116586666156365927/25000000000000000000 : ℝ)=(12616586666156365927/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(7944960429733/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5999/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (7944960429733/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(7944960429733/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5999/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (7944960429733/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(7944960429733/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5999/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (7944960429733/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-554400799/5000000000 : ℝ)*X 0 0+(2793542331/5000000000 : ℝ)*X 0 1+(624830187/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1765_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2677493089/5000000000 : ℝ)*X 1 0+(-711170747/5000000000 : ℝ)*X 1 1+(4998641041/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1765_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5354983041/10000000000 : ℝ)*X 2 0+(2499321551/5000000000 : ℝ)*X 2 1+(-44448217/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1765_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((988971509/2500000000 : ℝ)*X 0 0+(2997209989/10000000000 : ℝ)*X 0 1+(5049299039/10000000000 : ℝ)*X 0 2+(988971509/2500000000 : ℝ)*X 1 0+(2997209989/10000000000 : ℝ)*X 1 1+(5049299039/10000000000 : ℝ)*X 1 2+(988971509/2500000000 : ℝ)*X 2 0+(2997209989/10000000000 : ℝ)*X 2 1+(5049299039/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1765_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-55494451/500000000 : ℝ)*X 0 0+(5013283287/10000000000 : ℝ)*X 0 1+(5571984471/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1765_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1299778649/2500000000 : ℝ)*X 1 0+(-424499969/5000000000 : ℝ)*X 1 1+(1114396893/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1765_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1299778717/2500000000 : ℝ)*X 2 0+(5571984441/10000000000 : ℝ)*X 2 1+(-848999579/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1765_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((494959421/1250000000 : ℝ)*X 0 0+(1249560459/2500000000 : ℝ)*X 0 1+(3049868527/10000000000 : ℝ)*X 0 2+(494959421/1250000000 : ℝ)*X 1 0+(1249560459/2500000000 : ℝ)*X 1 1+(3049868527/10000000000 : ℝ)*X 1 2+(494959421/1250000000 : ℝ)*X 2 0+(1249560459/2500000000 : ℝ)*X 2 1+(3049868527/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1765_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (52276180147722178028331/6250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (425717289/100000000000000 : ℝ)*(base1) + (132724877/100000000000000 : ℝ)*(base16) + (826528391/50000000000000 : ℝ)*(base19) + (395126927/50000000000000 : ℝ)*(base23) + (112589067/25000000000000 : ℝ)*(upper3) + (68334903525073/6250000000000 : ℝ)*(major0) + (68334903525073/6250000000000 : ℝ)*(major1) + (68334903525073/6250000000000 : ℝ)*(major2) + (849703596092083/50000000000000 : ℝ)*(sp0) + (106212833016877/6250000000000 : ℝ)*(sp1) + (1699406323797837/100000000000000 : ℝ)*(sp2) + (24365409630057/5000000000000 : ℝ)*(sp3) + (347584813/100000000000000 : ℝ)*(sp4) + (450812957/50000000000000 : ℝ)*(sp7) + (487309519944343/100000000000000 : ℝ)*(f.failure) + (169940711405169/10000000000000 : ℝ)*(f.sum) + (13189090604491/12500000000000000000000000000 : ℝ)*base66 + (133999074479491/25000000000000000000000000000 : ℝ)*base68 + (192463989729491/25000000000000000000000000000 : ℝ)*base70 + (299711007004491/25000000000000000000000000000 : ℝ)*base72 + (32009101754491/12500000000000000000000000000 : ℝ)*base74 + (193773791054491/25000000000000000000000000000 : ℝ)*base76 + (245607622529491/25000000000000000000000000000 : ℝ)*base78 + (193918778254491/25000000000000000000000000000 : ℝ)*base80 + (30535142429491/12500000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (30876283/2500000000000000000000 : ℝ)*base89 + (30876283/2500000000000000000000 : ℝ)*base91 + (30876283/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (303176137842775566204513/25000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1663796099/100000000000000 : ℝ)*(base19) + (363410479/20000000000000 : ℝ)*(base23) + (7268961/3125000000000 : ℝ)*(base32) + (347146273/100000000000000 : ℝ)*(upper3) + (201797969/100000000000000 : ℝ)*(upper5) + (143944532088629/12500000000000 : ℝ)*(major0) + (143944532088629/12500000000000 : ℝ)*(major1) + (143944532088629/12500000000000 : ℝ)*(major2) + (6776240727/100000000000000 : ℝ)*(sp1) + (876495769/10000000000000 : ℝ)*(sp2) + (894931923978083/50000000000000 : ℝ)*(sp4) + (1789855407919341/100000000000000 : ℝ)*(sp5) + (1789853265946081/100000000000000 : ℝ)*(sp6) + (51324802862029/10000000000000 : ℝ)*(sp7) + (256624130613521/50000000000000 : ℝ)*(f.failure) + (894931923978083/50000000000000 : ℝ)*(f.sum) + (8134897806057/25000000000000000000000000000 : ℝ)*base65 + (58174621293943/50000000000000000000000000000 : ℝ)*base68 + (97797667993943/50000000000000000000000000000 : ℝ)*base70 + (60906585293943/50000000000000000000000000000 : ℝ)*base72 + (17372753293943/25000000000000000000000000000 : ℝ)*base74 + (380908477293943/50000000000000000000000000000 : ℝ)*base76 + (119731333093943/50000000000000000000000000000 : ℝ)*base78 + (1781255756057/50000000000000000000000000000 : ℝ)*base79 + (37253956468943/25000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (7133299/1250000000000000000000 : ℝ)*base90 + (7133299/1250000000000000000000 : ℝ)*base92 + (7133299/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1765_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5999/1024 : ℝ) ≤ p) (hpb : p ≤ (6015/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (56091581/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (7273/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (5011/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1765_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1765_s1_0 (p : ℝ) (hpa : (5999/1024 : ℝ) ≤ p) (hpb : p ≤ (6015/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-228578479/2000000000 : ℝ)*x 0 + (5479261971/10000000000 : ℝ)*x 1 + (2541739921/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (228578479/2000000000 : ℝ)^6015 ≤ (114434500949/1562500000000 : ℝ)^4991 := by
    have hnat : (228578479 : ℕ)^6015*1562500000000^4991 ≤ 114434500949^4991*2000000000^6015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      228578479 2000000000 114434500949 1562500000000 6015 4991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5479261971/10000000000 : ℝ)^6015 ≤ (48430154319881/100000000000000 : ℝ)^4991 := by
    have hnat : (5479261971 : ℕ)^6015*100000000000000^4991 ≤ 48430154319881^4991*10000000000^6015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5479261971 10000000000 48430154319881 100000000000000 6015 4991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2541739921/5000000000 : ℝ)^6015 ≤ (44246037604487/100000000000000 : ℝ)^4991 := by
    have hnat : (2541739921 : ℕ)^6015*100000000000000^4991 ≤ 44246037604487^4991*5000000000^6015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2541739921 5000000000 44246037604487 100000000000000 6015 4991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6015/1024 : ℝ)) 6015 4991 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-228578479/2000000000 : ℝ), (5479261971/10000000000 : ℝ), (2541739921/5000000000 : ℝ)] ![(114434500949/1562500000000 : ℝ), (48430154319881/100000000000000 : ℝ), (44246037604487/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-228578479/2000000000 : ℝ)|^6015 ≤ (114434500949/1562500000000 : ℝ)^4991
        have hw : |(-228578479/2000000000 : ℝ)|=(228578479/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5479261971/10000000000 : ℝ)|^6015 ≤ (48430154319881/100000000000000 : ℝ)^4991
        have hw : |(5479261971/10000000000 : ℝ)|=(5479261971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2541739921/5000000000 : ℝ)|^6015 ≤ (44246037604487/100000000000000 : ℝ)^4991
        have hw : |(2541739921/5000000000 : ℝ)|=(2541739921/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1765_s1_1 (p : ℝ) (hpa : (5999/1024 : ℝ) ≤ p) (hpb : p ≤ (6015/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (213055531/400000000 : ℝ)*x 0 + (-1349483971/10000000000 : ℝ)*x 1 + (5083479677/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (213055531/400000000 : ℝ)^6015 ≤ (46806399389349/100000000000000 : ℝ)^4991 := by
    have hnat : (213055531 : ℕ)^6015*100000000000000^4991 ≤ 46806399389349^4991*400000000^6015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      213055531 400000000 46806399389349 100000000000000 6015 4991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1349483971/10000000000 : ℝ)^6015 ≤ (8947564719939/100000000000000 : ℝ)^4991 := by
    have hnat : (1349483971 : ℕ)^6015*100000000000000^4991 ≤ 8947564719939^4991*10000000000^6015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1349483971 10000000000 8947564719939 100000000000000 6015 4991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5083479677/10000000000 : ℝ)^6015 ≤ (44246035873693/100000000000000 : ℝ)^4991 := by
    have hnat : (5083479677 : ℕ)^6015*100000000000000^4991 ≤ 44246035873693^4991*10000000000^6015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5083479677 10000000000 44246035873693 100000000000000 6015 4991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6015/1024 : ℝ)) 6015 4991 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(213055531/400000000 : ℝ), (-1349483971/10000000000 : ℝ), (5083479677/10000000000 : ℝ)] ![(46806399389349/100000000000000 : ℝ), (8947564719939/100000000000000 : ℝ), (44246035873693/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(213055531/400000000 : ℝ)|^6015 ≤ (46806399389349/100000000000000 : ℝ)^4991
        have hw : |(213055531/400000000 : ℝ)|=(213055531/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1349483971/10000000000 : ℝ)|^6015 ≤ (8947564719939/100000000000000 : ℝ)^4991
        have hw : |(-1349483971/10000000000 : ℝ)|=(1349483971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5083479677/10000000000 : ℝ)|^6015 ≤ (44246035873693/100000000000000 : ℝ)^4991
        have hw : |(5083479677/10000000000 : ℝ)|=(5083479677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1765_s1_2 (p : ℝ) (hpa : (5999/1024 : ℝ) ≤ p) (hpb : p ≤ (6015/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5326388141/10000000000 : ℝ)*x 0 + (5083479837/10000000000 : ℝ)*x 1 + (-674741969/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5326388141/10000000000 : ℝ)^6015 ≤ (1462699936569/3125000000000 : ℝ)^4991 := by
    have hnat : (5326388141 : ℕ)^6015*3125000000000^4991 ≤ 1462699936569^4991*10000000000^6015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5326388141 10000000000 1462699936569 3125000000000 6015 4991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5083479837/10000000000 : ℝ)^6015 ≤ (44246037552039/100000000000000 : ℝ)^4991 := by
    have hnat : (5083479837 : ℕ)^6015*100000000000000^4991 ≤ 44246037552039^4991*10000000000^6015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5083479837 10000000000 44246037552039 100000000000000 6015 4991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (674741969/5000000000 : ℝ)^6015 ≤ (4473782228123/50000000000000 : ℝ)^4991 := by
    have hnat : (674741969 : ℕ)^6015*50000000000000^4991 ≤ 4473782228123^4991*5000000000^6015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674741969 5000000000 4473782228123 50000000000000 6015 4991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6015/1024 : ℝ)) 6015 4991 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5326388141/10000000000 : ℝ), (5083479837/10000000000 : ℝ), (-674741969/5000000000 : ℝ)] ![(1462699936569/3125000000000 : ℝ), (44246037552039/100000000000000 : ℝ), (4473782228123/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5326388141/10000000000 : ℝ)|^6015 ≤ (1462699936569/3125000000000 : ℝ)^4991
        have hw : |(5326388141/10000000000 : ℝ)|=(5326388141/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5083479837/10000000000 : ℝ)|^6015 ≤ (44246037552039/100000000000000 : ℝ)^4991
        have hw : |(5083479837/10000000000 : ℝ)|=(5083479837/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-674741969/5000000000 : ℝ)|^6015 ≤ (4473782228123/50000000000000 : ℝ)^4991
        have hw : |(-674741969/5000000000 : ℝ)|=(674741969/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1765_s1_3 (p : ℝ) (hpa : (5999/1024 : ℝ) ≤ p) (hpb : p ≤ (6015/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (3990509519/10000000000 : ℝ)*x 0 + (666147971/2000000000 : ℝ)*x 1 + (4710961521/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3990509519/10000000000 : ℝ)^6015 ≤ (1322000461103/4000000000000 : ℝ)^4991 := by
    have hnat : (3990509519 : ℕ)^6015*4000000000000^4991 ≤ 1322000461103^4991*10000000000^6015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3990509519 10000000000 1322000461103 4000000000000 6015 4991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (666147971/2000000000 : ℝ)^6015 ≤ (26581575854551/100000000000000 : ℝ)^4991 := by
    have hnat : (666147971 : ℕ)^6015*100000000000000^4991 ≤ 26581575854551^4991*2000000000^6015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      666147971 2000000000 26581575854551 100000000000000 6015 4991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4710961521/10000000000 : ℝ)^6015 ≤ (630756446813/1562500000000 : ℝ)^4991 := by
    have hnat : (4710961521 : ℕ)^6015*1562500000000^4991 ≤ 630756446813^4991*10000000000^6015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4710961521 10000000000 630756446813 1562500000000 6015 4991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6015/1024 : ℝ)) 6015 4991 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3990509519/10000000000 : ℝ), (666147971/2000000000 : ℝ), (4710961521/10000000000 : ℝ)] ![(1322000461103/4000000000000 : ℝ), (26581575854551/100000000000000 : ℝ), (630756446813/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3990509519/10000000000 : ℝ)|^6015 ≤ (1322000461103/4000000000000 : ℝ)^4991
        have hw : |(3990509519/10000000000 : ℝ)|=(3990509519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(666147971/2000000000 : ℝ)|^6015 ≤ (26581575854551/100000000000000 : ℝ)^4991
        have hw : |(666147971/2000000000 : ℝ)|=(666147971/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4710961521/10000000000 : ℝ)|^6015 ≤ (630756446813/1562500000000 : ℝ)^4991
        have hw : |(4710961521/10000000000 : ℝ)|=(4710961521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1765_s1_4 (p : ℝ) (hpa : (5999/1024 : ℝ) ≤ p) (hpb : p ≤ (6015/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-71451369/625000000 : ℝ)*x 0 + (254506199/500000000 : ℝ)*x 1 + (2736239307/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (71451369/625000000 : ℝ)^6015 ≤ (1831588224181/25000000000000 : ℝ)^4991 := by
    have hnat : (71451369 : ℕ)^6015*25000000000000^4991 ≤ 1831588224181^4991*625000000^6015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      71451369 625000000 1831588224181 25000000000000 6015 4991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (254506199/500000000 : ℝ)^6015 ≤ (44315741682971/100000000000000 : ℝ)^4991 := by
    have hnat : (254506199 : ℕ)^6015*100000000000000^4991 ≤ 44315741682971^4991*500000000^6015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      254506199 500000000 44315741682971 100000000000000 6015 4991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2736239307/5000000000 : ℝ)^6015 ≤ (48357905402049/100000000000000 : ℝ)^4991 := by
    have hnat : (2736239307 : ℕ)^6015*100000000000000^4991 ≤ 48357905402049^4991*5000000000^6015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2736239307 5000000000 48357905402049 100000000000000 6015 4991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6015/1024 : ℝ)) 6015 4991 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-71451369/625000000 : ℝ), (254506199/500000000 : ℝ), (2736239307/5000000000 : ℝ)] ![(1831588224181/25000000000000 : ℝ), (44315741682971/100000000000000 : ℝ), (48357905402049/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-71451369/625000000 : ℝ)|^6015 ≤ (1831588224181/25000000000000 : ℝ)^4991
        have hw : |(-71451369/625000000 : ℝ)|=(71451369/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(254506199/500000000 : ℝ)|^6015 ≤ (44315741682971/100000000000000 : ℝ)^4991
        have hw : |(254506199/500000000 : ℝ)|=(254506199/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2736239307/5000000000 : ℝ)|^6015 ≤ (48357905402049/100000000000000 : ℝ)^4991
        have hw : |(2736239307/5000000000 : ℝ)|=(2736239307/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1765_s1_5 (p : ℝ) (hpa : (5999/1024 : ℝ) ≤ p) (hpb : p ≤ (6015/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1044395889/2000000000 : ℝ)*x 0 + (-240121273/2500000000 : ℝ)*x 1 + (2736239233/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1044395889/2000000000 : ℝ)^6015 ≤ (22851441327521/50000000000000 : ℝ)^4991 := by
    have hnat : (1044395889 : ℕ)^6015*50000000000000^4991 ≤ 22851441327521^4991*2000000000^6015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1044395889 2000000000 22851441327521 50000000000000 6015 4991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (240121273/2500000000 : ℝ)^6015 ≤ (5939213509793/100000000000000 : ℝ)^4991 := by
    have hnat : (240121273 : ℕ)^6015*100000000000000^4991 ≤ 5939213509793^4991*2500000000^6015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      240121273 2500000000 5939213509793 100000000000000 6015 4991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2736239233/5000000000 : ℝ)^6015 ≤ (9671580765183/20000000000000 : ℝ)^4991 := by
    have hnat : (2736239233 : ℕ)^6015*20000000000000^4991 ≤ 9671580765183^4991*5000000000^6015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2736239233 5000000000 9671580765183 20000000000000 6015 4991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6015/1024 : ℝ)) 6015 4991 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1044395889/2000000000 : ℝ), (-240121273/2500000000 : ℝ), (2736239233/5000000000 : ℝ)] ![(22851441327521/50000000000000 : ℝ), (5939213509793/100000000000000 : ℝ), (9671580765183/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1044395889/2000000000 : ℝ)|^6015 ≤ (22851441327521/50000000000000 : ℝ)^4991
        have hw : |(1044395889/2000000000 : ℝ)|=(1044395889/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-240121273/2500000000 : ℝ)|^6015 ≤ (5939213509793/100000000000000 : ℝ)^4991
        have hw : |(-240121273/2500000000 : ℝ)|=(240121273/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2736239233/5000000000 : ℝ)|^6015 ≤ (9671580765183/20000000000000 : ℝ)^4991
        have hw : |(2736239233/5000000000 : ℝ)|=(2736239233/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1765_s1_6 (p : ℝ) (hpa : (5999/1024 : ℝ) ≤ p) (hpb : p ≤ (6015/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2610989759/5000000000 : ℝ)*x 0 + (5472478459/10000000000 : ℝ)*x 1 + (-480242499/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2610989759/5000000000 : ℝ)^6015 ≤ (22851441712511/50000000000000 : ℝ)^4991 := by
    have hnat : (2610989759 : ℕ)^6015*50000000000000^4991 ≤ 22851441712511^4991*5000000000^6015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2610989759 5000000000 22851441712511 50000000000000 6015 4991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5472478459/10000000000 : ℝ)^6015 ≤ (6044737968921/12500000000000 : ℝ)^4991 := by
    have hnat : (5472478459 : ℕ)^6015*12500000000000^4991 ≤ 6044737968921^4991*10000000000^6015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5472478459 10000000000 6044737968921 12500000000000 6015 4991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (480242499/5000000000 : ℝ)^6015 ≤ (1484803202321/25000000000000 : ℝ)^4991 := by
    have hnat : (480242499 : ℕ)^6015*25000000000000^4991 ≤ 1484803202321^4991*5000000000^6015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      480242499 5000000000 1484803202321 25000000000000 6015 4991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6015/1024 : ℝ)) 6015 4991 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2610989759/5000000000 : ℝ), (5472478459/10000000000 : ℝ), (-480242499/5000000000 : ℝ)] ![(22851441712511/50000000000000 : ℝ), (6044737968921/12500000000000 : ℝ), (1484803202321/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2610989759/5000000000 : ℝ)|^6015 ≤ (22851441712511/50000000000000 : ℝ)^4991
        have hw : |(2610989759/5000000000 : ℝ)|=(2610989759/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5472478459/10000000000 : ℝ)|^6015 ≤ (6044737968921/12500000000000 : ℝ)^4991
        have hw : |(5472478459/10000000000 : ℝ)|=(5472478459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-480242499/5000000000 : ℝ)|^6015 ≤ (1484803202321/25000000000000 : ℝ)^4991
        have hw : |(-480242499/5000000000 : ℝ)|=(480242499/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1765_s1_7 (p : ℝ) (hpa : (5999/1024 : ℝ) ≤ p) (hpb : p ≤ (6015/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1995829413/5000000000 : ℝ)*x 0 + (4687791523/10000000000 : ℝ)*x 1 + (1677197739/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1995829413/5000000000 : ℝ)^6015 ≤ (33061483555833/100000000000000 : ℝ)^4991 := by
    have hnat : (1995829413 : ℕ)^6015*100000000000000^4991 ≤ 33061483555833^4991*5000000000^6015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1995829413 5000000000 33061483555833 100000000000000 6015 4991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4687791523/10000000000 : ℝ)^6015 ≤ (10032313401461/25000000000000 : ℝ)^4991 := by
    have hnat : (4687791523 : ℕ)^6015*25000000000000^4991 ≤ 10032313401461^4991*10000000000^6015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4687791523 10000000000 10032313401461 25000000000000 6015 4991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1677197739/5000000000 : ℝ)^6015 ≤ (13404631410623/50000000000000 : ℝ)^4991 := by
    have hnat : (1677197739 : ℕ)^6015*50000000000000^4991 ≤ 13404631410623^4991*5000000000^6015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1677197739 5000000000 13404631410623 50000000000000 6015 4991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6015/1024 : ℝ)) 6015 4991 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1995829413/5000000000 : ℝ), (4687791523/10000000000 : ℝ), (1677197739/5000000000 : ℝ)] ![(33061483555833/100000000000000 : ℝ), (10032313401461/25000000000000 : ℝ), (13404631410623/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1995829413/5000000000 : ℝ)|^6015 ≤ (33061483555833/100000000000000 : ℝ)^4991
        have hw : |(1995829413/5000000000 : ℝ)|=(1995829413/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4687791523/10000000000 : ℝ)|^6015 ≤ (10032313401461/25000000000000 : ℝ)^4991
        have hw : |(4687791523/10000000000 : ℝ)|=(4687791523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1677197739/5000000000 : ℝ)|^6015 ≤ (13404631410623/50000000000000 : ℝ)^4991
        have hw : |(1677197739/5000000000 : ℝ)|=(1677197739/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1765_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5999/1024 : ℝ) ≤ p) (hpb : p ≤ (6015/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (56091581/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (5011/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (7273/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (367/4000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (17723/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (5011/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (7273/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (5011/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (7273/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (5011/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (7273/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (5011/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (7273/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (5011/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (7273/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (5011/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (7273/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (7273/100000 : ℝ) ^ (5999/1024 : ℝ) ≤ (10725922739249/50000000000000000000 : ℝ) := by
    have hpowers : (7273/100000 : ℝ)^5999 ≤ (10725922739249/50000000000000000000 : ℝ)^1024 := by
      have hnat : (7273 : ℕ)^5999*50000000000000000000^1024 ≤ 10725922739249^1024*100000^5999 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7273 100000 10725922739249 50000000000000000000 5999 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7273/100000 : ℝ)) (X := (10725922739249/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5999 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (5011/25000 : ℝ) ^ (5999/1024 : ℝ) ≤ (8142288096981413/100000000000000000000 : ℝ) := by
    have hpowers : (5011/25000 : ℝ)^5999 ≤ (8142288096981413/100000000000000000000 : ℝ)^1024 := by
      have hnat : (5011 : ℕ)^5999*100000000000000000000^1024 ≤ 8142288096981413^1024*25000^5999 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5011 25000 8142288096981413 100000000000000000000 5999 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5011/25000 : ℝ)) (X := (8142288096981413/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5999 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000010725922739249/25000000000000000000 : ℝ) ≤ (250000018308623/250000000000000 : ℝ) ^ (5999/1024 : ℝ) := by
    have hpowers : (25000010725922739249/25000000000000000000 : ℝ)^1024 ≤ (250000018308623/250000000000000 : ℝ)^5999 := by
      have hnat : (25000010725922739249 : ℕ)^1024*250000000000000^5999 ≤ 250000018308623^5999*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000010725922739249 25000000000000000000 250000018308623 250000000000000 1024 5999 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (250000018308623/250000000000000 : ℝ)) (X := (25000010725922739249/25000000000000000000 : ℝ)) (by norm_num) 5999 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100008163739942459911/100000000000000000000 : ℝ) ≤ (10000139346336569/10000000000000000 : ℝ) ^ (5999/1024 : ℝ) := by
    have hpowers : (100008163739942459911/100000000000000000000 : ℝ)^1024 ≤ (10000139346336569/10000000000000000 : ℝ)^5999 := by
      have hnat : (100008163739942459911 : ℕ)^1024*10000000000000000^5999 ≤ 10000139346336569^5999*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100008163739942459911 100000000000000000000 10000139346336569 10000000000000000 1024 5999 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000139346336569/10000000000000000 : ℝ)) (X := (100008163739942459911/100000000000000000000 : ℝ)) (by norm_num) 5999 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50008142288096981413/50000000000000000000 : ℝ) ≤ (5000138980164109/5000000000000000 : ℝ) ^ (5999/1024 : ℝ) := by
    have hpowers : (50008142288096981413/50000000000000000000 : ℝ)^1024 ≤ (5000138980164109/5000000000000000 : ℝ)^5999 := by
      have hnat : (50008142288096981413 : ℕ)^1024*5000000000000000^5999 ≤ 5000138980164109^5999*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50008142288096981413 50000000000000000000 5000138980164109 5000000000000000 1024 5999 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000138980164109/5000000000000000 : ℝ)) (X := (50008142288096981413/50000000000000000000 : ℝ)) (by norm_num) 5999 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10725922739249/50000000000000000000 : ℝ) ≤ ((21284665512275741161/21285000000000000000 : ℝ)+2*(46204663883/425700000000000 : ℝ)*(7273/100000 : ℝ))^(5999/1024 : ℝ) := by
    rw [show (21284665512275741161/21285000000000000000 : ℝ)+2*(46204663883/425700000000000 : ℝ)*(7273/100000 : ℝ)=(250000018308623/250000000000000 : ℝ) by norm_num, show 1+2*(10725922739249/50000000000000000000 : ℝ)=(25000010725922739249/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(8142288096981413/100000000000000000000 : ℝ)+(10725922739249/50000000000000000000 : ℝ) ≤ ((21284665512275741161/21285000000000000000 : ℝ)+(46204663883/425700000000000 : ℝ)*((5011/25000 : ℝ)+(7273/100000 : ℝ)))^(5999/1024 : ℝ) := by
    rw [show (21284665512275741161/21285000000000000000 : ℝ)+(46204663883/425700000000000 : ℝ)*((5011/25000 : ℝ)+(7273/100000 : ℝ))=(10000139346336569/10000000000000000 : ℝ) by norm_num, show 1+(8142288096981413/100000000000000000000 : ℝ)+(10725922739249/50000000000000000000 : ℝ)=(100008163739942459911/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(8142288096981413/100000000000000000000 : ℝ) ≤ ((21284665512275741161/21285000000000000000 : ℝ)+2*(46204663883/425700000000000 : ℝ)*(5011/25000 : ℝ))^(5999/1024 : ℝ) := by
    rw [show (21284665512275741161/21285000000000000000 : ℝ)+2*(46204663883/425700000000000 : ℝ)*(5011/25000 : ℝ)=(5000138980164109/5000000000000000 : ℝ) by norm_num, show 1+2*(8142288096981413/100000000000000000000 : ℝ)=(50008142288096981413/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (21284665512275741161/21285000000000000000 : ℝ)*(X 1 0+X 2 0)+(46204663883/425700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5999/1024 : ℝ)) (lo := (7273/100000 : ℝ)) (hi := (5011/25000 : ℝ)) (c := (21284665512275741161/21285000000000000000 : ℝ)) (alpha := (46204663883/425700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (21284665512275741161/21285000000000000000 : ℝ)*(X 0 1+X 2 1)+(46204663883/425700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5999/1024 : ℝ)) (lo := (7273/100000 : ℝ)) (hi := (5011/25000 : ℝ)) (c := (21284665512275741161/21285000000000000000 : ℝ)) (alpha := (46204663883/425700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (21284665512275741161/21285000000000000000 : ℝ)*(X 0 2+X 1 2)+(46204663883/425700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5999/1024 : ℝ)) (lo := (7273/100000 : ℝ)) (hi := (5011/25000 : ℝ)) (c := (21284665512275741161/21285000000000000000 : ℝ)) (alpha := (46204663883/425700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-228578479/2000000000 : ℝ)*X 0 0+(5479261971/10000000000 : ℝ)*X 0 1+(2541739921/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1765_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((213055531/400000000 : ℝ)*X 1 0+(-1349483971/10000000000 : ℝ)*X 1 1+(5083479677/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1765_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5326388141/10000000000 : ℝ)*X 2 0+(5083479837/10000000000 : ℝ)*X 2 1+(-674741969/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1765_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((3990509519/10000000000 : ℝ)*X 0 0+(666147971/2000000000 : ℝ)*X 0 1+(4710961521/10000000000 : ℝ)*X 0 2+(3990509519/10000000000 : ℝ)*X 1 0+(666147971/2000000000 : ℝ)*X 1 1+(4710961521/10000000000 : ℝ)*X 1 2+(3990509519/10000000000 : ℝ)*X 2 0+(666147971/2000000000 : ℝ)*X 2 1+(4710961521/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1765_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-71451369/625000000 : ℝ)*X 0 0+(254506199/500000000 : ℝ)*X 0 1+(2736239307/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1765_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1044395889/2000000000 : ℝ)*X 1 0+(-240121273/2500000000 : ℝ)*X 1 1+(2736239233/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1765_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2610989759/5000000000 : ℝ)*X 2 0+(5472478459/10000000000 : ℝ)*X 2 1+(-480242499/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1765_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1995829413/5000000000 : ℝ)*X 0 0+(4687791523/10000000000 : ℝ)*X 0 1+(1677197739/5000000000 : ℝ)*X 0 2+(1995829413/5000000000 : ℝ)*X 1 0+(4687791523/10000000000 : ℝ)*X 1 1+(1677197739/5000000000 : ℝ)*X 1 2+(1995829413/5000000000 : ℝ)*X 2 0+(4687791523/10000000000 : ℝ)*X 2 1+(1677197739/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1765_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (9323596668150122781007579/739062500000000000000000000000 : ℝ) := by norm_num
    linear_combination (832139081/50000000000000 : ℝ)*(base19) + (298058763/20000000000000 : ℝ)*(base23) + (58813487/100000000000000 : ℝ)*(lower2) + (716969/250000000000 : ℝ)*(upper3) + (216778473/100000000000000 : ℝ)*(upper5) + (20319982656983/1250000000000 : ℝ)*(major0) + (20319982656983/1250000000000 : ℝ)*(major1) + (20319982656983/1250000000000 : ℝ)*(major2) + (1263327712036039/50000000000000 : ℝ)*(sp0) + (126333317513687/5000000000000 : ℝ)*(sp1) + (2526666524258087/100000000000000 : ℝ)*(sp2) + (724524779776609/100000000000000 : ℝ)*(sp3) + (503619193/4000000000000 : ℝ)*(sp4) + (4010274183/100000000000000 : ℝ)*(sp7) + (90566098756349/12500000000000 : ℝ)*(f.failure) + (1263334007275951/50000000000000 : ℝ)*(f.sum) + (11356327312741/4257000000000000000000000000 : ℝ)*base65 + (67857056268335237/26606250000000000000000000000000 : ℝ)*base68 + (66247241168046013/26606250000000000000000000000000 : ℝ)*base69 + (176176078360671013/26606250000000000000000000000000 : ℝ)*base71 + (1286279438639/266062500000000000000000000 : ℝ)*base74 + (377599757863183513/26606250000000000000000000000000 : ℝ)*base75 + (132442114334927263/26606250000000000000000000000000 : ℝ)*base77 + (337578490810933513/26606250000000000000000000000000 : ℝ)*base79 + (350371593941/170280000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (802231/312500000000000000000 : ℝ)*base90 + (802231/312500000000000000000 : ℝ)*base92 + (802231/312500000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (478366081962582364302750203/59125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1004367279/100000000000000 : ℝ)*(base19) + (1189912481/100000000000000 : ℝ)*(base23) + (16713803/10000000000000 : ℝ)*(upper3) + (1782173/3125000000000 : ℝ)*(lower4) + (124200033/100000000000000 : ℝ)*(upper5) + (841334210881477/50000000000000 : ℝ)*(major0) + (841334210881477/50000000000000 : ℝ)*(major1) + (841334210881477/50000000000000 : ℝ)*(major2) + (6398064033/100000000000000 : ℝ)*(sp1) + (1677467187/20000000000000 : ℝ)*(sp2) + (52307435755607/2000000000000 : ℝ)*(sp4) + (1307682192674519/50000000000000 : ℝ)*(sp5) + (1307681105265967/50000000000000 : ℝ)*(sp6) + (187491196513403/25000000000000 : ℝ)*(sp7) + (187491196513403/25000000000000 : ℝ)*(f.failure) + (52307435755607/2000000000000 : ℝ)*(f.sum) + (30800409599269/10642500000000000000000000000 : ℝ)*base66 + (2069451033177924797/1064250000000000000000000000000000 : ℝ)*base67 + (5562875752797924797/1064250000000000000000000000000000 : ℝ)*base69 + (395393849128674797/1064250000000000000000000000000000 : ℝ)*base71 + (112435389329663/21285000000000000000000000000 : ℝ)*base74 + (7324701027724674797/1064250000000000000000000000000000 : ℝ)*base75 + (2158709592345174797/1064250000000000000000000000000000 : ℝ)*base77 + (9565113522088674797/1064250000000000000000000000000000 : ℝ)*base79 + (1971942570319/665156250000000000000000000 : ℝ)*base82 + (539857/625000000000000000000 : ℝ)*base90 + (539857/625000000000000000000 : ℝ)*base92 + (539857/625000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1765_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5999/1024 : ℝ) ≤ p) (hpb : p ≤ (6015/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (56091581/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (5011/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (7273/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (367/4000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17723/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1765_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1765_s2_0 (p : ℝ) (hpa : (5999/1024 : ℝ) ≤ p) (hpb : p ≤ (6015/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-45736697/400000000 : ℝ)*x 0 + (1069838/1953125 : ℝ)*x 1 + (5084810817/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (45736697/400000000 : ℝ)^6015 ≤ (732786299909/10000000000000 : ℝ)^4991 := by
    have hnat : (45736697 : ℕ)^6015*10000000000000^4991 ≤ 732786299909^4991*400000000^6015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      45736697 400000000 732786299909 10000000000000 6015 4991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1069838/1953125 : ℝ)^6015 ≤ (24206068768477/50000000000000 : ℝ)^4991 := by
    have hnat : (1069838 : ℕ)^6015*50000000000000^4991 ≤ 24206068768477^4991*1953125^6015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069838 1953125 24206068768477 50000000000000 6015 4991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5084810817/10000000000 : ℝ)^6015 ≤ (44259999452373/100000000000000 : ℝ)^4991 := by
    have hnat : (5084810817 : ℕ)^6015*100000000000000^4991 ≤ 44259999452373^4991*10000000000^6015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5084810817 10000000000 44259999452373 100000000000000 6015 4991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6015/1024 : ℝ)) 6015 4991 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-45736697/400000000 : ℝ), (1069838/1953125 : ℝ), (5084810817/10000000000 : ℝ)] ![(732786299909/10000000000000 : ℝ), (24206068768477/50000000000000 : ℝ), (44259999452373/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-45736697/400000000 : ℝ)|^6015 ≤ (732786299909/10000000000000 : ℝ)^4991
        have hw : |(-45736697/400000000 : ℝ)|=(45736697/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1069838/1953125 : ℝ)|^6015 ≤ (24206068768477/50000000000000 : ℝ)^4991
        have hw : |(1069838/1953125 : ℝ)|=(1069838/1953125 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5084810817/10000000000 : ℝ)|^6015 ≤ (44259999452373/100000000000000 : ℝ)^4991
        have hw : |(5084810817/10000000000 : ℝ)|=(5084810817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1765_s2_1 (p : ℝ) (hpa : (5999/1024 : ℝ) ≤ p) (hpb : p ≤ (6015/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (532591413/1000000000 : ℝ)*x 0 + (-1348364813/10000000000 : ℝ)*x 1 + (5084810813/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (532591413/1000000000 : ℝ)^6015 ≤ (365635765283/781250000000 : ℝ)^4991 := by
    have hnat : (532591413 : ℕ)^6015*781250000000^4991 ≤ 365635765283^4991*1000000000^6015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      532591413 1000000000 365635765283 781250000000 6015 4991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1348364813/10000000000 : ℝ)^6015 ≤ (8938622617811/100000000000000 : ℝ)^4991 := by
    have hnat : (1348364813 : ℕ)^6015*100000000000000^4991 ≤ 8938622617811^4991*10000000000^6015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348364813 10000000000 8938622617811 100000000000000 6015 4991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5084810813/10000000000 : ℝ)^6015 ≤ (11064999852603/25000000000000 : ℝ)^4991 := by
    have hnat : (5084810813 : ℕ)^6015*25000000000000^4991 ≤ 11064999852603^4991*10000000000^6015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5084810813 10000000000 11064999852603 25000000000000 6015 4991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6015/1024 : ℝ)) 6015 4991 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(532591413/1000000000 : ℝ), (-1348364813/10000000000 : ℝ), (5084810813/10000000000 : ℝ)] ![(365635765283/781250000000 : ℝ), (8938622617811/100000000000000 : ℝ), (11064999852603/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(532591413/1000000000 : ℝ)|^6015 ≤ (365635765283/781250000000 : ℝ)^4991
        have hw : |(532591413/1000000000 : ℝ)|=(532591413/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1348364813/10000000000 : ℝ)|^6015 ≤ (8938622617811/100000000000000 : ℝ)^4991
        have hw : |(-1348364813/10000000000 : ℝ)|=(1348364813/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5084810813/10000000000 : ℝ)|^6015 ≤ (11064999852603/25000000000000 : ℝ)^4991
        have hw : |(5084810813/10000000000 : ℝ)|=(5084810813/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1765_s2_2 (p : ℝ) (hpa : (5999/1024 : ℝ) ≤ p) (hpb : p ≤ (6015/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (532591413/1000000000 : ℝ)*x 0 + (1016962163/2000000000 : ℝ)*x 1 + (-134836481/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (532591413/1000000000 : ℝ)^6015 ≤ (365635765283/781250000000 : ℝ)^4991 := by
    have hnat : (532591413 : ℕ)^6015*781250000000^4991 ≤ 365635765283^4991*1000000000^6015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      532591413 1000000000 365635765283 781250000000 6015 4991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1016962163/2000000000 : ℝ)^6015 ≤ (1383124982231/3125000000000 : ℝ)^4991 := by
    have hnat : (1016962163 : ℕ)^6015*3125000000000^4991 ≤ 1383124982231^4991*2000000000^6015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1016962163 2000000000 1383124982231 3125000000000 6015 4991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (134836481/1000000000 : ℝ)^6015 ≤ (8938622593843/100000000000000 : ℝ)^4991 := by
    have hnat : (134836481 : ℕ)^6015*100000000000000^4991 ≤ 8938622593843^4991*1000000000^6015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      134836481 1000000000 8938622593843 100000000000000 6015 4991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6015/1024 : ℝ)) 6015 4991 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(532591413/1000000000 : ℝ), (1016962163/2000000000 : ℝ), (-134836481/1000000000 : ℝ)] ![(365635765283/781250000000 : ℝ), (1383124982231/3125000000000 : ℝ), (8938622593843/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(532591413/1000000000 : ℝ)|^6015 ≤ (365635765283/781250000000 : ℝ)^4991
        have hw : |(532591413/1000000000 : ℝ)|=(532591413/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1016962163/2000000000 : ℝ)|^6015 ≤ (1383124982231/3125000000000 : ℝ)^4991
        have hw : |(1016962163/2000000000 : ℝ)|=(1016962163/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-134836481/1000000000 : ℝ)|^6015 ≤ (8938622593843/100000000000000 : ℝ)^4991
        have hw : |(-134836481/1000000000 : ℝ)|=(134836481/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1765_s2_3 (p : ℝ) (hpa : (5999/1024 : ℝ) ≤ p) (hpb : p ≤ (6015/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (498867849/1250000000 : ℝ)*x 0 + (41699747/125000000 : ℝ)*x 1 + (4705661221/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (498867849/1250000000 : ℝ)^6015 ≤ (3305433624553/10000000000000 : ℝ)^4991 := by
    have hnat : (498867849 : ℕ)^6015*10000000000000^4991 ≤ 3305433624553^4991*1250000000^6015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      498867849 1250000000 3305433624553 10000000000000 6015 4991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (41699747/125000000 : ℝ)^6015 ≤ (26631981773799/100000000000000 : ℝ)^4991 := by
    have hnat : (41699747 : ℕ)^6015*100000000000000^4991 ≤ 26631981773799^4991*125000000^6015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41699747 125000000 26631981773799 100000000000000 6015 4991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4705661221/10000000000 : ℝ)^6015 ≤ (40313681961247/100000000000000 : ℝ)^4991 := by
    have hnat : (4705661221 : ℕ)^6015*100000000000000^4991 ≤ 40313681961247^4991*10000000000^6015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4705661221 10000000000 40313681961247 100000000000000 6015 4991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6015/1024 : ℝ)) 6015 4991 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(498867849/1250000000 : ℝ), (41699747/125000000 : ℝ), (4705661221/10000000000 : ℝ)] ![(3305433624553/10000000000000 : ℝ), (26631981773799/100000000000000 : ℝ), (40313681961247/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(498867849/1250000000 : ℝ)|^6015 ≤ (3305433624553/10000000000000 : ℝ)^4991
        have hw : |(498867849/1250000000 : ℝ)|=(498867849/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(41699747/125000000 : ℝ)|^6015 ≤ (26631981773799/100000000000000 : ℝ)^4991
        have hw : |(41699747/125000000 : ℝ)|=(41699747/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4705661221/10000000000 : ℝ)|^6015 ≤ (40313681961247/100000000000000 : ℝ)^4991
        have hw : |(4705661221/10000000000 : ℝ)|=(4705661221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1765_s2_4 (p : ℝ) (hpa : (5999/1024 : ℝ) ≤ p) (hpb : p ≤ (6015/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-285934869/2500000000 : ℝ)*x 0 + (5091353873/10000000000 : ℝ)*x 1 + (5470891411/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (285934869/2500000000 : ℝ)^6015 ≤ (733035046877/10000000000000 : ℝ)^4991 := by
    have hnat : (285934869 : ℕ)^6015*10000000000000^4991 ≤ 733035046877^4991*2500000000^6015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      285934869 2500000000 733035046877 10000000000000 6015 4991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5091353873/10000000000 : ℝ)^6015 ≤ (44328646617843/100000000000000 : ℝ)^4991 := by
    have hnat : (5091353873 : ℕ)^6015*100000000000000^4991 ≤ 44328646617843^4991*10000000000^6015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5091353873 10000000000 44328646617843 100000000000000 6015 4991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5470891411/10000000000 : ℝ)^6015 ≤ (48341002898997/100000000000000 : ℝ)^4991 := by
    have hnat : (5470891411 : ℕ)^6015*100000000000000^4991 ≤ 48341002898997^4991*10000000000^6015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5470891411 10000000000 48341002898997 100000000000000 6015 4991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6015/1024 : ℝ)) 6015 4991 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-285934869/2500000000 : ℝ), (5091353873/10000000000 : ℝ), (5470891411/10000000000 : ℝ)] ![(733035046877/10000000000000 : ℝ), (44328646617843/100000000000000 : ℝ), (48341002898997/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-285934869/2500000000 : ℝ)|^6015 ≤ (733035046877/10000000000000 : ℝ)^4991
        have hw : |(-285934869/2500000000 : ℝ)|=(285934869/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5091353873/10000000000 : ℝ)|^6015 ≤ (44328646617843/100000000000000 : ℝ)^4991
        have hw : |(5091353873/10000000000 : ℝ)|=(5091353873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5470891411/10000000000 : ℝ)|^6015 ≤ (48341002898997/100000000000000 : ℝ)^4991
        have hw : |(5470891411/10000000000 : ℝ)|=(5470891411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1765_s2_5 (p : ℝ) (hpa : (5999/1024 : ℝ) ≤ p) (hpb : p ≤ (6015/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2611155201/5000000000 : ℝ)*x 0 + (-192456843/2000000000 : ℝ)*x 1 + (1367722853/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2611155201/5000000000 : ℝ)^6015 ≤ (9141274700533/20000000000000 : ℝ)^4991 := by
    have hnat : (2611155201 : ℕ)^6015*20000000000000^4991 ≤ 9141274700533^4991*5000000000^6015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2611155201 5000000000 9141274700533 20000000000000 6015 4991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (192456843/2000000000 : ℝ)^6015 ≤ (238104942679/4000000000000 : ℝ)^4991 := by
    have hnat : (192456843 : ℕ)^6015*4000000000000^4991 ≤ 238104942679^4991*2000000000^6015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      192456843 2000000000 238104942679 4000000000000 6015 4991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1367722853/2500000000 : ℝ)^6015 ≤ (24170501454823/50000000000000 : ℝ)^4991 := by
    have hnat : (1367722853 : ℕ)^6015*50000000000000^4991 ≤ 24170501454823^4991*2500000000^6015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1367722853 2500000000 24170501454823 50000000000000 6015 4991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6015/1024 : ℝ)) 6015 4991 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2611155201/5000000000 : ℝ), (-192456843/2000000000 : ℝ), (1367722853/2500000000 : ℝ)] ![(9141274700533/20000000000000 : ℝ), (238104942679/4000000000000 : ℝ), (24170501454823/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2611155201/5000000000 : ℝ)|^6015 ≤ (9141274700533/20000000000000 : ℝ)^4991
        have hw : |(2611155201/5000000000 : ℝ)|=(2611155201/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-192456843/2000000000 : ℝ)|^6015 ≤ (238104942679/4000000000000 : ℝ)^4991
        have hw : |(-192456843/2000000000 : ℝ)|=(192456843/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1367722853/2500000000 : ℝ)|^6015 ≤ (24170501454823/50000000000000 : ℝ)^4991
        have hw : |(1367722853/2500000000 : ℝ)|=(1367722853/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1765_s2_6 (p : ℝ) (hpa : (5999/1024 : ℝ) ≤ p) (hpb : p ≤ (6015/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1305577601/2500000000 : ℝ)*x 0 + (1367722853/2500000000 : ℝ)*x 1 + (-481142107/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1305577601/2500000000 : ℝ)^6015 ≤ (45706373523761/100000000000000 : ℝ)^4991 := by
    have hnat : (1305577601 : ℕ)^6015*100000000000000^4991 ≤ 45706373523761^4991*2500000000^6015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1305577601 2500000000 45706373523761 100000000000000 6015 4991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1367722853/2500000000 : ℝ)^6015 ≤ (24170501454823/50000000000000 : ℝ)^4991 := by
    have hnat : (1367722853 : ℕ)^6015*50000000000000^4991 ≤ 24170501454823^4991*2500000000^6015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1367722853 2500000000 24170501454823 50000000000000 6015 4991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (481142107/5000000000 : ℝ)^6015 ≤ (37203897247/625000000000 : ℝ)^4991 := by
    have hnat : (481142107 : ℕ)^6015*625000000000^4991 ≤ 37203897247^4991*5000000000^6015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      481142107 5000000000 37203897247 625000000000 6015 4991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6015/1024 : ℝ)) 6015 4991 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1305577601/2500000000 : ℝ), (1367722853/2500000000 : ℝ), (-481142107/5000000000 : ℝ)] ![(45706373523761/100000000000000 : ℝ), (24170501454823/50000000000000 : ℝ), (37203897247/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1305577601/2500000000 : ℝ)|^6015 ≤ (45706373523761/100000000000000 : ℝ)^4991
        have hw : |(1305577601/2500000000 : ℝ)|=(1305577601/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1367722853/2500000000 : ℝ)|^6015 ≤ (24170501454823/50000000000000 : ℝ)^4991
        have hw : |(1367722853/2500000000 : ℝ)|=(1367722853/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-481142107/5000000000 : ℝ)|^6015 ≤ (37203897247/625000000000 : ℝ)^4991
        have hw : |(-481142107/5000000000 : ℝ)|=(481142107/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1765_s2_7 (p : ℝ) (hpa : (5999/1024 : ℝ) ≤ p) (hpb : p ≤ (6015/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (3992065867/10000000000 : ℝ)*x 0 + (4682843447/10000000000 : ℝ)*x 1 + (839818033/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3992065867/10000000000 : ℝ)^6015 ≤ (33065546676167/100000000000000 : ℝ)^4991 := by
    have hnat : (3992065867 : ℕ)^6015*100000000000000^4991 ≤ 33065546676167^4991*10000000000^6015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3992065867 10000000000 33065546676167 100000000000000 6015 4991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4682843447/10000000000 : ℝ)^6015 ≤ (40078211313019/100000000000000 : ℝ)^4991 := by
    have hnat : (4682843447 : ℕ)^6015*100000000000000^4991 ≤ 40078211313019^4991*10000000000^6015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4682843447 10000000000 40078211313019 100000000000000 6015 4991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (839818033/2500000000 : ℝ)^6015 ≤ (1342812099639/5000000000000 : ℝ)^4991 := by
    have hnat : (839818033 : ℕ)^6015*5000000000000^4991 ≤ 1342812099639^4991*2500000000^6015 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      839818033 2500000000 1342812099639 5000000000000 6015 4991 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6015/1024 : ℝ)) 6015 4991 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3992065867/10000000000 : ℝ), (4682843447/10000000000 : ℝ), (839818033/2500000000 : ℝ)] ![(33065546676167/100000000000000 : ℝ), (40078211313019/100000000000000 : ℝ), (1342812099639/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3992065867/10000000000 : ℝ)|^6015 ≤ (33065546676167/100000000000000 : ℝ)^4991
        have hw : |(3992065867/10000000000 : ℝ)|=(3992065867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4682843447/10000000000 : ℝ)|^6015 ≤ (40078211313019/100000000000000 : ℝ)^4991
        have hw : |(4682843447/10000000000 : ℝ)|=(4682843447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(839818033/2500000000 : ℝ)|^6015 ≤ (1342812099639/5000000000000 : ℝ)^4991
        have hw : |(839818033/2500000000 : ℝ)|=(839818033/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1765_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5999/1024 : ℝ) ≤ p) (hpb : p ≤ (6015/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (56091581/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17723/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (367/4000 : ℝ)*pair X i i ≤ pair X i h) :
    (1841/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (17687/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (17723/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (367/4000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (17723/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (367/4000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (17723/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (367/4000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (17723/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (367/4000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (17723/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (367/4000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (17723/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (367/4000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (367/4000 : ℝ) ^ (5999/1024 : ℝ) ≤ (83662923912223/100000000000000000000 : ℝ) := by
    have hpowers : (367/4000 : ℝ)^5999 ≤ (83662923912223/100000000000000000000 : ℝ)^1024 := by
      have hnat : (367 : ℕ)^5999*100000000000000000000^1024 ≤ 83662923912223^1024*4000^5999 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        367 4000 83662923912223 100000000000000000000 5999 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (367/4000 : ℝ)) (X := (83662923912223/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5999 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (17723/100000 : ℝ) ^ (5999/1024 : ℝ) ≤ (791884280332813/20000000000000000000 : ℝ) := by
    have hpowers : (17723/100000 : ℝ)^5999 ≤ (791884280332813/20000000000000000000 : ℝ)^1024 := by
      have hnat : (17723 : ℕ)^5999*20000000000000000000^1024 ≤ 791884280332813^1024*100000^5999 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17723 100000 791884280332813 20000000000000000000 5999 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (17723/100000 : ℝ)) (X := (791884280332813/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5999 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000083662923912223/50000000000000000000 : ℝ) ≤ (10000002856168517/10000000000000000 : ℝ) ^ (5999/1024 : ℝ) := by
    have hpowers : (50000083662923912223/50000000000000000000 : ℝ)^1024 ≤ (10000002856168517/10000000000000000 : ℝ)^5999 := by
      have hnat : (50000083662923912223 : ℕ)^1024*10000000000000000^5999 ≤ 10000002856168517^5999*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000083662923912223 50000000000000000000 10000002856168517 10000000000000000 1024 5999 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000002856168517/10000000000000000 : ℝ)) (X := (50000083662923912223/50000000000000000000 : ℝ)) (by norm_num) 5999 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (3125126346385174259/3125000000000000000 : ℝ) ≤ (10000069012317771/10000000000000000 : ℝ) ^ (5999/1024 : ℝ) := by
    have hpowers : (3125126346385174259/3125000000000000000 : ℝ)^1024 ≤ (10000069012317771/10000000000000000 : ℝ)^5999 := by
      have hnat : (3125126346385174259 : ℕ)^1024*10000000000000000^5999 ≤ 10000069012317771^5999*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3125126346385174259 3125000000000000000 10000069012317771 10000000000000000 1024 5999 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000069012317771/10000000000000000 : ℝ)) (X := (3125126346385174259/3125000000000000000 : ℝ)) (by norm_num) 5999 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10000791884280332813/10000000000000000000 : ℝ) ≤ (400005406738681/400000000000000 : ℝ) ^ (5999/1024 : ℝ) := by
    have hpowers : (10000791884280332813/10000000000000000000 : ℝ)^1024 ≤ (400005406738681/400000000000000 : ℝ)^5999 := by
      have hnat : (10000791884280332813 : ℕ)^1024*400000000000000^5999 ≤ 400005406738681^5999*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000791884280332813 10000000000000000000 400005406738681 400000000000000 1024 5999 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400005406738681/400000000000000 : ℝ)) (X := (10000791884280332813/10000000000000000000 : ℝ)) (by norm_num) 5999 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(83662923912223/100000000000000000000 : ℝ) ≤ ((2671212826537177263/2671250000000000000 : ℝ)+2*(33078074627/427400000000000 : ℝ)*(367/4000 : ℝ))^(5999/1024 : ℝ) := by
    rw [show (2671212826537177263/2671250000000000000 : ℝ)+2*(33078074627/427400000000000 : ℝ)*(367/4000 : ℝ)=(10000002856168517/10000000000000000 : ℝ) by norm_num, show 1+2*(83662923912223/100000000000000000000 : ℝ)=(50000083662923912223/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(791884280332813/20000000000000000000 : ℝ)+(83662923912223/100000000000000000000 : ℝ) ≤ ((2671212826537177263/2671250000000000000 : ℝ)+(33078074627/427400000000000 : ℝ)*((17723/100000 : ℝ)+(367/4000 : ℝ)))^(5999/1024 : ℝ) := by
    rw [show (2671212826537177263/2671250000000000000 : ℝ)+(33078074627/427400000000000 : ℝ)*((17723/100000 : ℝ)+(367/4000 : ℝ))=(10000069012317771/10000000000000000 : ℝ) by norm_num, show 1+(791884280332813/20000000000000000000 : ℝ)+(83662923912223/100000000000000000000 : ℝ)=(3125126346385174259/3125000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(791884280332813/20000000000000000000 : ℝ) ≤ ((2671212826537177263/2671250000000000000 : ℝ)+2*(33078074627/427400000000000 : ℝ)*(17723/100000 : ℝ))^(5999/1024 : ℝ) := by
    rw [show (2671212826537177263/2671250000000000000 : ℝ)+2*(33078074627/427400000000000 : ℝ)*(17723/100000 : ℝ)=(400005406738681/400000000000000 : ℝ) by norm_num, show 1+2*(791884280332813/20000000000000000000 : ℝ)=(10000791884280332813/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2671212826537177263/2671250000000000000 : ℝ)*(X 1 0+X 2 0)+(33078074627/427400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5999/1024 : ℝ)) (lo := (367/4000 : ℝ)) (hi := (17723/100000 : ℝ)) (c := (2671212826537177263/2671250000000000000 : ℝ)) (alpha := (33078074627/427400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2671212826537177263/2671250000000000000 : ℝ)*(X 0 1+X 2 1)+(33078074627/427400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5999/1024 : ℝ)) (lo := (367/4000 : ℝ)) (hi := (17723/100000 : ℝ)) (c := (2671212826537177263/2671250000000000000 : ℝ)) (alpha := (33078074627/427400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2671212826537177263/2671250000000000000 : ℝ)*(X 0 2+X 1 2)+(33078074627/427400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5999/1024 : ℝ)) (lo := (367/4000 : ℝ)) (hi := (17723/100000 : ℝ)) (c := (2671212826537177263/2671250000000000000 : ℝ)) (alpha := (33078074627/427400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-45736697/400000000 : ℝ)*X 0 0+(1069838/1953125 : ℝ)*X 0 1+(5084810817/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1765_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((532591413/1000000000 : ℝ)*X 1 0+(-1348364813/10000000000 : ℝ)*X 1 1+(5084810813/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1765_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((532591413/1000000000 : ℝ)*X 2 0+(1016962163/2000000000 : ℝ)*X 2 1+(-134836481/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1765_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((498867849/1250000000 : ℝ)*X 0 0+(41699747/125000000 : ℝ)*X 0 1+(4705661221/10000000000 : ℝ)*X 0 2+(498867849/1250000000 : ℝ)*X 1 0+(41699747/125000000 : ℝ)*X 1 1+(4705661221/10000000000 : ℝ)*X 1 2+(498867849/1250000000 : ℝ)*X 2 0+(41699747/125000000 : ℝ)*X 2 1+(4705661221/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1765_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-285934869/2500000000 : ℝ)*X 0 0+(5091353873/10000000000 : ℝ)*X 0 1+(5470891411/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1765_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2611155201/5000000000 : ℝ)*X 1 0+(-192456843/2000000000 : ℝ)*X 1 1+(1367722853/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1765_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1305577601/2500000000 : ℝ)*X 2 0+(1367722853/2500000000 : ℝ)*X 2 1+(-481142107/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1765_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((3992065867/10000000000 : ℝ)*X 0 0+(4682843447/10000000000 : ℝ)*X 0 1+(839818033/2500000000 : ℝ)*X 0 2+(3992065867/10000000000 : ℝ)*X 1 0+(4682843447/10000000000 : ℝ)*X 1 1+(839818033/2500000000 : ℝ)*X 1 2+(3992065867/10000000000 : ℝ)*X 2 0+(4682843447/10000000000 : ℝ)*X 2 1+(839818033/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1765_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5049021159671355198021/667812500000000000000000000 : ℝ) := by norm_num
    linear_combination (100810353/10000000000000 : ℝ)*(base19) + (7432063/781250000000 : ℝ)*(base23) + (7562727/25000000000000 : ℝ)*(lower2) + (179129869/100000000000000 : ℝ)*(upper3) + (70405217/50000000000000 : ℝ)*(upper5) + (102381372005259/6250000000000 : ℝ)*(major0) + (102381372005259/6250000000000 : ℝ)*(major1) + (102381372005259/6250000000000 : ℝ)*(major2) + (2546093959529621/100000000000000 : ℝ)*(sp0) + (159131319969017/6250000000000 : ℝ)*(sp1) + (1273050588151869/50000000000000 : ℝ)*(sp2) + (365049492977127/50000000000000 : ℝ)*(sp3) + (408403909/5000000000000 : ℝ)*(sp4) + (1269294163/50000000000000 : ℝ)*(sp7) + (36505076227129/5000000000000 : ℝ)*(f.failure) + (2546102127607801/100000000000000 : ℝ)*(f.sum) + (10700617293281/10685000000000000000000000000 : ℝ)*base66 + (5670481943337249/2086914062500000000000000000000 : ℝ)*base67 + (78054880941244641/33390625000000000000000000000000 : ℝ)*base70 + (1027093153833371/8347656250000000000000000000000 : ℝ)*base71 + (2383572563333/5342500000000000000000000000 : ℝ)*base74 + (7036446950881501/2086914062500000000000000000000 : ℝ)*base76 + (6582899628752623/4173828125000000000000000000000 : ℝ)*base77 + (97547644977442633/16695312500000000000000000000000 : ℝ)*base80 + (25825061546133/5342500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (700949/125000000000000000000 : ℝ)*base89 + (700949/125000000000000000000 : ℝ)*base91 + (700949/125000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1395931129474093460340736179/133562500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (261817683/20000000000000 : ℝ)*(base19) + (1399782899/100000000000000 : ℝ)*(base23) + (367391759/100000000000000 : ℝ)*(lower1) + (225772077/100000000000000 : ℝ)*(upper3) + (19823639/50000000000000 : ℝ)*(lower4) + (108539827/50000000000000 : ℝ)*(upper5) + (1695152174421489/100000000000000 : ℝ)*(major0) + (1695152174421489/100000000000000 : ℝ)*(major1) + (1695152174421489/100000000000000 : ℝ)*(major2) + (693917379/100000000000000 : ℝ)*(sp2) + (526955041954803/20000000000000 : ℝ)*(sp4) + (3293467375857/125000000000 : ℝ)*(sp5) + (1317386558036869/50000000000000 : ℝ)*(sp6) + (151105758136991/20000000000000 : ℝ)*(sp7) + (151105758136991/20000000000000 : ℝ)*(f.failure) + (526955041954803/20000000000000 : ℝ)*(f.sum) + (74238240778047/21370000000000000000000000000 : ℝ)*base66 + (1899478050034423357/267125000000000000000000000000000 : ℝ)*base67 + (190596817963798357/267125000000000000000000000000000 : ℝ)*base69 + (2893478969773798357/267125000000000000000000000000000 : ℝ)*base71 + (113945529597153/21370000000000000000000000000 : ℝ)*base73 + (714807716864423357/267125000000000000000000000000000 : ℝ)*base75 + (217358400527951643/267125000000000000000000000000000 : ℝ)*base78 + (2671987500578326643/267125000000000000000000000000000 : ℝ)*base80 + (65022477980543/21370000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (5227229/500000000000000000000 : ℝ)*base90 + (5227229/500000000000000000000 : ℝ)*base92 + (5227229/500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1765_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5999/1024 : ℝ) ≤ p) (hpb : p ≤ (6015/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (56091581/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17723/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (367/4000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1841/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17687/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1765_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1765_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5999/1024 : ℝ) ≤ p) (hpb : p ≤ (6015/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (56091581/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1841/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17687/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1765_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1765_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1765_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5999/1024 : ℝ) ≤ p) (hpb : p ≤ (6015/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (56091581/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1841/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17687/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1765_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
