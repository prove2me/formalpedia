-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1098_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:59:36.535394+00:00
-- url     : https://prove2.me/submissions/96c1ba68-8598-4026-888f-80979a2f281b

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
theorem support_rectangle_w1098_s6_0 (p : ℝ) (hpa : (4145/1024 : ℝ) ≤ p) (hpb : p ≤ (8291/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-437613343/2000000000 : ℝ)*x 0 + (16857081/31250000 : ℝ)*x 1 + (5264581611/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (437613343/2000000000 : ℝ)^8291 ≤ (13291351195737/100000000000000 : ℝ)^6243 := by
    have hnat : (437613343 : ℕ)^8291*100000000000000^6243 ≤ 13291351195737^6243*2000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      437613343 2000000000 13291351195737 100000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (16857081/31250000 : ℝ)^8291 ≤ (44054822268417/100000000000000 : ℝ)^6243 := by
    have hnat : (16857081 : ℕ)^8291*100000000000000^6243 ≤ 44054822268417^6243*31250000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16857081 31250000 44054822268417 100000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264581611/10000000000 : ℝ)^8291 ≤ (1706153061103/4000000000000 : ℝ)^6243 := by
    have hnat : (5264581611 : ℕ)^8291*4000000000000^6243 ≤ 1706153061103^6243*10000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264581611 10000000000 1706153061103 4000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8291/2048 : ℝ)) 8291 6243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-437613343/2000000000 : ℝ), (16857081/31250000 : ℝ), (5264581611/10000000000 : ℝ)] ![(13291351195737/100000000000000 : ℝ), (44054822268417/100000000000000 : ℝ), (1706153061103/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-437613343/2000000000 : ℝ)|^8291 ≤ (13291351195737/100000000000000 : ℝ)^6243
        have hw : |(-437613343/2000000000 : ℝ)|=(437613343/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(16857081/31250000 : ℝ)|^8291 ≤ (44054822268417/100000000000000 : ℝ)^6243
        have hw : |(16857081/31250000 : ℝ)|=(16857081/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264581611/10000000000 : ℝ)|^8291 ≤ (1706153061103/4000000000000 : ℝ)^6243
        have hw : |(5264581611/10000000000 : ℝ)|=(5264581611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1098_s6_1 (p : ℝ) (hpa : (4145/1024 : ℝ) ≤ p) (hpb : p ≤ (8291/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1069002841/2000000000 : ℝ)*x 0 + (-1126931319/5000000000 : ℝ)*x 1 + (2632290809/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069002841/2000000000 : ℝ)^8291 ≤ (21760716781237/50000000000000 : ℝ)^6243 := by
    have hnat : (1069002841 : ℕ)^8291*50000000000000^6243 ≤ 21760716781237^6243*2000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069002841 2000000000 21760716781237 50000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1126931319/5000000000 : ℝ)^8291 ≤ (6912369905683/50000000000000 : ℝ)^6243 := by
    have hnat : (1126931319 : ℕ)^8291*50000000000000^6243 ≤ 6912369905683^6243*5000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1126931319 5000000000 6912369905683 50000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632290809/5000000000 : ℝ)^8291 ≤ (8530765320579/20000000000000 : ℝ)^6243 := by
    have hnat : (2632290809 : ℕ)^8291*20000000000000^6243 ≤ 8530765320579^6243*5000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632290809 5000000000 8530765320579 20000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8291/2048 : ℝ)) 8291 6243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069002841/2000000000 : ℝ), (-1126931319/5000000000 : ℝ), (2632290809/5000000000 : ℝ)] ![(21760716781237/50000000000000 : ℝ), (6912369905683/50000000000000 : ℝ), (8530765320579/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069002841/2000000000 : ℝ)|^8291 ≤ (21760716781237/50000000000000 : ℝ)^6243
        have hw : |(1069002841/2000000000 : ℝ)|=(1069002841/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1126931319/5000000000 : ℝ)|^8291 ≤ (6912369905683/50000000000000 : ℝ)^6243
        have hw : |(-1126931319/5000000000 : ℝ)|=(1126931319/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632290809/5000000000 : ℝ)|^8291 ≤ (8530765320579/20000000000000 : ℝ)^6243
        have hw : |(2632290809/5000000000 : ℝ)|=(2632290809/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1098_s6_2 (p : ℝ) (hpa : (4145/1024 : ℝ) ≤ p) (hpb : p ≤ (8291/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5345014201/10000000000 : ℝ)*x 0 + (2632290809/5000000000 : ℝ)*x 1 + (-563465661/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345014201/10000000000 : ℝ)^8291 ≤ (2176071675961/5000000000000 : ℝ)^6243 := by
    have hnat : (5345014201 : ℕ)^8291*5000000000000^6243 ≤ 2176071675961^6243*10000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345014201 10000000000 2176071675961 5000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632290809/5000000000 : ℝ)^8291 ≤ (8530765320579/20000000000000 : ℝ)^6243 := by
    have hnat : (2632290809 : ℕ)^8291*20000000000000^6243 ≤ 8530765320579^6243*5000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632290809 5000000000 8530765320579 20000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (563465661/2500000000 : ℝ)^8291 ≤ (6912369930121/50000000000000 : ℝ)^6243 := by
    have hnat : (563465661 : ℕ)^8291*50000000000000^6243 ≤ 6912369930121^6243*2500000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      563465661 2500000000 6912369930121 50000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8291/2048 : ℝ)) 8291 6243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345014201/10000000000 : ℝ), (2632290809/5000000000 : ℝ), (-563465661/2500000000 : ℝ)] ![(2176071675961/5000000000000 : ℝ), (8530765320579/20000000000000 : ℝ), (6912369930121/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345014201/10000000000 : ℝ)|^8291 ≤ (2176071675961/5000000000000 : ℝ)^6243
        have hw : |(5345014201/10000000000 : ℝ)|=(5345014201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632290809/5000000000 : ℝ)|^8291 ≤ (8530765320579/20000000000000 : ℝ)^6243
        have hw : |(2632290809/5000000000 : ℝ)|=(2632290809/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-563465661/2500000000 : ℝ)|^8291 ≤ (6912369930121/50000000000000 : ℝ)^6243
        have hw : |(-563465661/2500000000 : ℝ)|=(563465661/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1098_s6_3 (p : ℝ) (hpa : (4145/1024 : ℝ) ≤ p) (hpb : p ≤ (8291/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2185443351/5000000000 : ℝ)*x 0 + (2122439237/5000000000 : ℝ)*x 1 + (562582157/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2185443351/5000000000 : ℝ)^8291 ≤ (33316496052233/100000000000000 : ℝ)^6243 := by
    have hnat : (2185443351 : ℕ)^8291*100000000000000^6243 ≤ 33316496052233^6243*5000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2185443351 5000000000 33316496052233 100000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2122439237/5000000000 : ℝ)^8291 ≤ (16023501576213/50000000000000 : ℝ)^6243 := by
    have hnat : (2122439237 : ℕ)^8291*50000000000000^6243 ≤ 16023501576213^6243*5000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2122439237 5000000000 16023501576213 50000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (562582157/1250000000 : ℝ)^8291 ≤ (1731825039251/5000000000000 : ℝ)^6243 := by
    have hnat : (562582157 : ℕ)^8291*5000000000000^6243 ≤ 1731825039251^6243*1250000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      562582157 1250000000 1731825039251 5000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8291/2048 : ℝ)) 8291 6243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2185443351/5000000000 : ℝ), (2122439237/5000000000 : ℝ), (562582157/1250000000 : ℝ)] ![(33316496052233/100000000000000 : ℝ), (16023501576213/50000000000000 : ℝ), (1731825039251/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2185443351/5000000000 : ℝ)|^8291 ≤ (33316496052233/100000000000000 : ℝ)^6243
        have hw : |(2185443351/5000000000 : ℝ)|=(2185443351/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2122439237/5000000000 : ℝ)|^8291 ≤ (16023501576213/50000000000000 : ℝ)^6243
        have hw : |(2122439237/5000000000 : ℝ)|=(2122439237/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(562582157/1250000000 : ℝ)|^8291 ≤ (1731825039251/5000000000000 : ℝ)^6243
        have hw : |(562582157/1250000000 : ℝ)|=(562582157/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1098_s6_4 (p : ℝ) (hpa : (4145/1024 : ℝ) ≤ p) (hpb : p ≤ (8291/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2188071843/10000000000 : ℝ)*x 0 + (5264909077/10000000000 : ℝ)*x 1 + (5393937237/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2188071843/10000000000 : ℝ)^8291 ≤ (13291392564291/100000000000000 : ℝ)^6243 := by
    have hnat : (2188071843 : ℕ)^8291*100000000000000^6243 ≤ 13291392564291^6243*10000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2188071843 10000000000 13291392564291 100000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264909077/10000000000 : ℝ)^8291 ≤ (21328675030363/50000000000000 : ℝ)^6243 := by
    have hnat : (5264909077 : ℕ)^8291*50000000000000^6243 ≤ 21328675030363^6243*10000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264909077 10000000000 21328675030363 50000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5393937237/10000000000 : ℝ)^8291 ≤ (11012814341629/25000000000000 : ℝ)^6243 := by
    have hnat : (5393937237 : ℕ)^8291*25000000000000^6243 ≤ 11012814341629^6243*10000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393937237 10000000000 11012814341629 25000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8291/2048 : ℝ)) 8291 6243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2188071843/10000000000 : ℝ), (5264909077/10000000000 : ℝ), (5393937237/10000000000 : ℝ)] ![(13291392564291/100000000000000 : ℝ), (21328675030363/50000000000000 : ℝ), (11012814341629/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2188071843/10000000000 : ℝ)|^8291 ≤ (13291392564291/100000000000000 : ℝ)^6243
        have hw : |(-2188071843/10000000000 : ℝ)|=(2188071843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264909077/10000000000 : ℝ)|^8291 ≤ (21328675030363/50000000000000 : ℝ)^6243
        have hw : |(5264909077/10000000000 : ℝ)|=(5264909077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5393937237/10000000000 : ℝ)|^8291 ≤ (11012814341629/25000000000000 : ℝ)^6243
        have hw : |(5393937237/10000000000 : ℝ)|=(5393937237/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1098_s6_5 (p : ℝ) (hpa : (4145/1024 : ℝ) ≤ p) (hpb : p ≤ (8291/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2656133683/5000000000 : ℝ)*x 0 + (-1062253497/5000000000 : ℝ)*x 1 + (2696968611/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656133683/5000000000 : ℝ)^8291 ≤ (43167680632167/100000000000000 : ℝ)^6243 := by
    have hnat : (2656133683 : ℕ)^8291*100000000000000^6243 ≤ 43167680632167^6243*5000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656133683 5000000000 43167680632167 100000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1062253497/5000000000 : ℝ)^8291 ≤ (399408192061/3125000000000 : ℝ)^6243 := by
    have hnat : (1062253497 : ℕ)^8291*3125000000000^6243 ≤ 399408192061^6243*5000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062253497 5000000000 399408192061 3125000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2696968611/5000000000 : ℝ)^8291 ≤ (44051257203827/100000000000000 : ℝ)^6243 := by
    have hnat : (2696968611 : ℕ)^8291*100000000000000^6243 ≤ 44051257203827^6243*5000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696968611 5000000000 44051257203827 100000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8291/2048 : ℝ)) 8291 6243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656133683/5000000000 : ℝ), (-1062253497/5000000000 : ℝ), (2696968611/5000000000 : ℝ)] ![(43167680632167/100000000000000 : ℝ), (399408192061/3125000000000 : ℝ), (44051257203827/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656133683/5000000000 : ℝ)|^8291 ≤ (43167680632167/100000000000000 : ℝ)^6243
        have hw : |(2656133683/5000000000 : ℝ)|=(2656133683/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1062253497/5000000000 : ℝ)|^8291 ≤ (399408192061/3125000000000 : ℝ)^6243
        have hw : |(-1062253497/5000000000 : ℝ)|=(1062253497/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2696968611/5000000000 : ℝ)|^8291 ≤ (44051257203827/100000000000000 : ℝ)^6243
        have hw : |(2696968611/5000000000 : ℝ)|=(2696968611/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1098_s6_6 (p : ℝ) (hpa : (4145/1024 : ℝ) ≤ p) (hpb : p ≤ (8291/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312267363/10000000000 : ℝ)*x 0 + (2696968607/5000000000 : ℝ)*x 1 + (-2124507009/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312267363/10000000000 : ℝ)^8291 ≤ (2697980037487/6250000000000 : ℝ)^6243 := by
    have hnat : (5312267363 : ℕ)^8291*6250000000000^6243 ≤ 2697980037487^6243*10000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312267363 10000000000 2697980037487 6250000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2696968607/5000000000 : ℝ)^8291 ≤ (2202562855853/5000000000000 : ℝ)^6243 := by
    have hnat : (2696968607 : ℕ)^8291*5000000000000^6243 ≤ 2202562855853^6243*5000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696968607 5000000000 2202562855853 5000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2124507009/10000000000 : ℝ)^8291 ≤ (3195265566449/25000000000000 : ℝ)^6243 := by
    have hnat : (2124507009 : ℕ)^8291*25000000000000^6243 ≤ 3195265566449^6243*10000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2124507009 10000000000 3195265566449 25000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8291/2048 : ℝ)) 8291 6243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312267363/10000000000 : ℝ), (2696968607/5000000000 : ℝ), (-2124507009/10000000000 : ℝ)] ![(2697980037487/6250000000000 : ℝ), (2202562855853/5000000000000 : ℝ), (3195265566449/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312267363/10000000000 : ℝ)|^8291 ≤ (2697980037487/6250000000000 : ℝ)^6243
        have hw : |(5312267363/10000000000 : ℝ)|=(5312267363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2696968607/5000000000 : ℝ)|^8291 ≤ (2202562855853/5000000000000 : ℝ)^6243
        have hw : |(2696968607/5000000000 : ℝ)|=(2696968607/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2124507009/10000000000 : ℝ)|^8291 ≤ (3195265566449/25000000000000 : ℝ)^6243
        have hw : |(-2124507009/10000000000 : ℝ)|=(2124507009/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1098_s6_7 (p : ℝ) (hpa : (4145/1024 : ℝ) ≤ p) (hpb : p ≤ (8291/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4370896769/10000000000 : ℝ)*x 0 + (4500011329/10000000000 : ℝ)*x 1 + (2122763361/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4370896769/10000000000 : ℝ)^8291 ≤ (33316597959131/100000000000000 : ℝ)^6243 := by
    have hnat : (4370896769 : ℕ)^8291*100000000000000^6243 ≤ 33316597959131^6243*10000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4370896769 10000000000 33316597959131 100000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4500011329/10000000000 : ℝ)^8291 ≤ (17314949625511/50000000000000 : ℝ)^6243 := by
    have hnat : (4500011329 : ℕ)^8291*50000000000000^6243 ≤ 17314949625511^6243*10000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4500011329 10000000000 17314949625511 50000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2122763361/5000000000 : ℝ)^8291 ≤ (1001671961563/3125000000000 : ℝ)^6243 := by
    have hnat : (2122763361 : ℕ)^8291*3125000000000^6243 ≤ 1001671961563^6243*5000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2122763361 5000000000 1001671961563 3125000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8291/2048 : ℝ)) 8291 6243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4370896769/10000000000 : ℝ), (4500011329/10000000000 : ℝ), (2122763361/5000000000 : ℝ)] ![(33316597959131/100000000000000 : ℝ), (17314949625511/50000000000000 : ℝ), (1001671961563/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4370896769/10000000000 : ℝ)|^8291 ≤ (33316597959131/100000000000000 : ℝ)^6243
        have hw : |(4370896769/10000000000 : ℝ)|=(4370896769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4500011329/10000000000 : ℝ)|^8291 ≤ (17314949625511/50000000000000 : ℝ)^6243
        have hw : |(4500011329/10000000000 : ℝ)|=(4500011329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2122763361/5000000000 : ℝ)|^8291 ≤ (1001671961563/3125000000000 : ℝ)^6243
        have hw : |(2122763361/5000000000 : ℝ)|=(2122763361/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1098_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4145/1024 : ℝ) ≤ p) (hpb : p ≤ (8291/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148615943/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14071/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11249/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5643/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14033/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14071/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11249/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14071/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11249/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14071/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11249/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14071/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11249/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14071/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11249/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14071/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11249/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11249/100000 : ℝ) ^ (4145/1024 : ℝ) ≤ (2884562684482149/20000000000000000000 : ℝ) := by
    have hpowers : (11249/100000 : ℝ)^4145 ≤ (2884562684482149/20000000000000000000 : ℝ)^1024 := by
      have hnat : (11249 : ℕ)^4145*20000000000000000000^1024 ≤ 2884562684482149^1024*100000^4145 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11249 100000 2884562684482149 20000000000000000000 4145 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11249/100000 : ℝ)) (X := (2884562684482149/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4145 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14071/100000 : ℝ) ^ (4145/1024 : ℝ) ≤ (35689944359651179/100000000000000000000 : ℝ) := by
    have hpowers : (14071/100000 : ℝ)^4145 ≤ (35689944359651179/100000000000000000000 : ℝ)^1024 := by
      have hnat : (14071 : ℕ)^4145*100000000000000000000^1024 ≤ 35689944359651179^1024*100000^4145 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14071 100000 35689944359651179 100000000000000000000 4145 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14071/100000 : ℝ)) (X := (35689944359651179/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4145 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10002884562684482149/10000000000000000000 : ℝ) ≤ (10000712538351983/10000000000000000 : ℝ) ^ (4145/1024 : ℝ) := by
    have hpowers : (10002884562684482149/10000000000000000000 : ℝ)^1024 ≤ (10000712538351983/10000000000000000 : ℝ)^4145 := by
      have hnat : (10002884562684482149 : ℕ)^1024*10000000000000000^4145 ≤ 10000712538351983^4145*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002884562684482149 10000000000000000000 10000712538351983 10000000000000000 1024 4145 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000712538351983/10000000000000000 : ℝ)) (X := (10002884562684482149/10000000000000000000 : ℝ)) (by norm_num) 4145 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25012528189445515481/25000000000000000000 : ℝ) ≤ (5000618887641199/5000000000000000 : ℝ) ^ (4145/1024 : ℝ) := by
    have hpowers : (25012528189445515481/25000000000000000000 : ℝ)^1024 ≤ (5000618887641199/5000000000000000 : ℝ)^4145 := by
      have hnat : (25012528189445515481 : ℕ)^1024*5000000000000000^4145 ≤ 5000618887641199^4145*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25012528189445515481 25000000000000000000 5000618887641199 5000000000000000 1024 4145 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000618887641199/5000000000000000 : ℝ)) (X := (25012528189445515481/25000000000000000000 : ℝ)) (by norm_num) 4145 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50035689944359651179/50000000000000000000 : ℝ) ≤ (10001763012212813/10000000000000000 : ℝ) ^ (4145/1024 : ℝ) := by
    have hpowers : (50035689944359651179/50000000000000000000 : ℝ)^1024 ≤ (10001763012212813/10000000000000000 : ℝ)^4145 := by
      have hnat : (50035689944359651179 : ℕ)^1024*10000000000000000^4145 ≤ 10001763012212813^4145*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50035689944359651179 50000000000000000000 10001763012212813 10000000000000000 1024 4145 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001763012212813/10000000000000000 : ℝ)) (X := (50035689944359651179/50000000000000000000 : ℝ)) (by norm_num) 4145 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2884562684482149/20000000000000000000 : ℝ) ≤ ((7052548500692204839/7055000000000000000 : ℝ)+2*(105047386083/56440000000000 : ℝ)*(11249/100000 : ℝ))^(4145/1024 : ℝ) := by
    rw [show (7052548500692204839/7055000000000000000 : ℝ)+2*(105047386083/56440000000000 : ℝ)*(11249/100000 : ℝ)=(10000712538351983/10000000000000000 : ℝ) by norm_num, show 1+2*(2884562684482149/20000000000000000000 : ℝ)=(10002884562684482149/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(35689944359651179/100000000000000000000 : ℝ)+(2884562684482149/20000000000000000000 : ℝ) ≤ ((7052548500692204839/7055000000000000000 : ℝ)+(105047386083/56440000000000 : ℝ)*((14071/100000 : ℝ)+(11249/100000 : ℝ)))^(4145/1024 : ℝ) := by
    rw [show (7052548500692204839/7055000000000000000 : ℝ)+(105047386083/56440000000000 : ℝ)*((14071/100000 : ℝ)+(11249/100000 : ℝ))=(5000618887641199/5000000000000000 : ℝ) by norm_num, show 1+(35689944359651179/100000000000000000000 : ℝ)+(2884562684482149/20000000000000000000 : ℝ)=(25012528189445515481/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(35689944359651179/100000000000000000000 : ℝ) ≤ ((7052548500692204839/7055000000000000000 : ℝ)+2*(105047386083/56440000000000 : ℝ)*(14071/100000 : ℝ))^(4145/1024 : ℝ) := by
    rw [show (7052548500692204839/7055000000000000000 : ℝ)+2*(105047386083/56440000000000 : ℝ)*(14071/100000 : ℝ)=(10001763012212813/10000000000000000 : ℝ) by norm_num, show 1+2*(35689944359651179/100000000000000000000 : ℝ)=(50035689944359651179/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (7052548500692204839/7055000000000000000 : ℝ)*(X 1 0+X 2 0)+(105047386083/56440000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4145/1024 : ℝ)) (lo := (11249/100000 : ℝ)) (hi := (14071/100000 : ℝ)) (c := (7052548500692204839/7055000000000000000 : ℝ)) (alpha := (105047386083/56440000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (7052548500692204839/7055000000000000000 : ℝ)*(X 0 1+X 2 1)+(105047386083/56440000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4145/1024 : ℝ)) (lo := (11249/100000 : ℝ)) (hi := (14071/100000 : ℝ)) (c := (7052548500692204839/7055000000000000000 : ℝ)) (alpha := (105047386083/56440000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (7052548500692204839/7055000000000000000 : ℝ)*(X 0 2+X 1 2)+(105047386083/56440000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4145/1024 : ℝ)) (lo := (11249/100000 : ℝ)) (hi := (14071/100000 : ℝ)) (c := (7052548500692204839/7055000000000000000 : ℝ)) (alpha := (105047386083/56440000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-437613343/2000000000 : ℝ)*X 0 0+(16857081/31250000 : ℝ)*X 0 1+(5264581611/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1098_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1069002841/2000000000 : ℝ)*X 1 0+(-1126931319/5000000000 : ℝ)*X 1 1+(2632290809/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1098_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5345014201/10000000000 : ℝ)*X 2 0+(2632290809/5000000000 : ℝ)*X 2 1+(-563465661/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1098_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2185443351/5000000000 : ℝ)*X 0 0+(2122439237/5000000000 : ℝ)*X 0 1+(562582157/1250000000 : ℝ)*X 0 2+(2185443351/5000000000 : ℝ)*X 1 0+(2122439237/5000000000 : ℝ)*X 1 1+(562582157/1250000000 : ℝ)*X 1 2+(2185443351/5000000000 : ℝ)*X 2 0+(2122439237/5000000000 : ℝ)*X 2 1+(562582157/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1098_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2188071843/10000000000 : ℝ)*X 0 0+(5264909077/10000000000 : ℝ)*X 0 1+(5393937237/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1098_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2656133683/5000000000 : ℝ)*X 1 0+(-1062253497/5000000000 : ℝ)*X 1 1+(2696968611/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1098_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312267363/10000000000 : ℝ)*X 2 0+(2696968607/5000000000 : ℝ)*X 2 1+(-2124507009/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1098_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4370896769/10000000000 : ℝ)*X 0 0+(4500011329/10000000000 : ℝ)*X 0 1+(2122763361/5000000000 : ℝ)*X 0 2+(4370896769/10000000000 : ℝ)*X 1 0+(4500011329/10000000000 : ℝ)*X 1 1+(2122763361/5000000000 : ℝ)*X 1 2+(4370896769/10000000000 : ℝ)*X 2 0+(4500011329/10000000000 : ℝ)*X 2 1+(2122763361/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1098_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (631351594465198505916335013/176375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (173162713/25000000000000 : ℝ)*(base19) + (643960827/100000000000000 : ℝ)*(base23) + (1147023/5000000000000 : ℝ)*(lower2) + (90938017/100000000000000 : ℝ)*(upper3) + (48953473/100000000000000 : ℝ)*(upper5) + (5810359934708411/100000000000000 : ℝ)*(major0) + (5810359934708411/100000000000000 : ℝ)*(major1) + (5810359934708411/100000000000000 : ℝ)*(major2) + (3855526607034691/50000000000000 : ℝ)*(sp0) + (240970977031543/3125000000000 : ℝ)*(sp1) + (7711071313699401/100000000000000 : ℝ)*(sp2) + (78192751474407/2000000000000 : ℝ)*(sp3) + (3748718169/20000000000000 : ℝ)*(sp4) + (102187163/1000000000000 : ℝ)*(sp7) + (78192955848733/2000000000000 : ℝ)*(f.failure) + (1927767989415057/25000000000000 : ℝ)*(f.sum) + (2018805278457/2822000000000000000000000000 : ℝ)*base66 + (10563809182584825829/705500000000000000000000000000000 : ℝ)*base67 + (171450066493825829/705500000000000000000000000000000 : ℝ)*base69 + (2857577929977674171/705500000000000000000000000000000 : ℝ)*base72 + (31861867726849/2822000000000000000000000000 : ℝ)*base73 + (8218297911938325829/705500000000000000000000000000000 : ℝ)*base75 + (4188950763956825829/705500000000000000000000000000000 : ℝ)*base77 + (2923562142263325829/705500000000000000000000000000000 : ℝ)*base79 + (7568293424281/2822000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1849781/200000000000000000000 : ℝ)*base90 + (1849781/200000000000000000000 : ℝ)*base92 + (1849781/200000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3458849843745463077828035481/352750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2034124047/100000000000000 : ℝ)*(base19) + (2128131187/100000000000000 : ℝ)*(base23) + (202964283/100000000000000 : ℝ)*(upper3) + (49843207/100000000000000 : ℝ)*(lower4) + (56767347/25000000000000 : ℝ)*(upper5) + (5839877983965431/100000000000000 : ℝ)*(major0) + (5839877983965431/100000000000000 : ℝ)*(major1) + (5839877983965431/100000000000000 : ℝ)*(major2) + (27920732811/50000000000000 : ℝ)*(sp1) + (28290383567/50000000000000 : ℝ)*(sp2) + (310009835273951/4000000000000 : ℝ)*(sp4) + (3875094003129553/50000000000000 : ℝ)*(sp5) + (7750187172950453/100000000000000 : ℝ)*(sp6) + (1964754879617939/50000000000000 : ℝ)*(sp7) + (1964754879617939/50000000000000 : ℝ)*(f.failure) + (310009835273951/4000000000000 : ℝ)*(f.sum) + (11031136308319/2822000000000000000000000000 : ℝ)*base65 + (8376153387009954391/705500000000000000000000000000000 : ℝ)*base68 + (7044292182106954391/705500000000000000000000000000000 : ℝ)*base70 + (2308557747940454391/705500000000000000000000000000000 : ℝ)*base72 + (3622517682609/2822000000000000000000000000 : ℝ)*base73 + (25891474408098454391/705500000000000000000000000000000 : ℝ)*base76 + (4029088865208954391/705500000000000000000000000000000 : ℝ)*base78 + (3840472777744454391/705500000000000000000000000000000 : ℝ)*base80 + (141521756427/2822000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (65798523/5000000000000000000000 : ℝ)*base90 + (65798523/5000000000000000000000 : ℝ)*base92 + (65798523/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1098_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4145/1024 : ℝ) ≤ p) (hpb : p ≤ (8291/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148615943/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14071/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11249/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5643/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14033/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1098_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1098_s7_0 (p : ℝ) (hpa : (4145/1024 : ℝ) ≤ p) (hpb : p ≤ (8291/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-547024687/2500000000 : ℝ)*x 0 + (2696935221/5000000000 : ℝ)*x 1 + (5264956233/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (547024687/2500000000 : ℝ)^8291 ≤ (13291609612577/100000000000000 : ℝ)^6243 := by
    have hnat : (547024687 : ℕ)^8291*100000000000000^6243 ≤ 13291609612577^6243*2500000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      547024687 2500000000 13291609612577 100000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2696935221/5000000000 : ℝ)^8291 ≤ (22025266457711/50000000000000 : ℝ)^6243 := by
    have hnat : (2696935221 : ℕ)^8291*50000000000000^6243 ≤ 22025266457711^6243*5000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696935221 5000000000 22025266457711 50000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264956233/10000000000 : ℝ)^8291 ≤ (42657857465063/100000000000000 : ℝ)^6243 := by
    have hnat : (5264956233 : ℕ)^8291*100000000000000^6243 ≤ 42657857465063^6243*10000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264956233 10000000000 42657857465063 100000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8291/2048 : ℝ)) 8291 6243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-547024687/2500000000 : ℝ), (2696935221/5000000000 : ℝ), (5264956233/10000000000 : ℝ)] ![(13291609612577/100000000000000 : ℝ), (22025266457711/50000000000000 : ℝ), (42657857465063/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-547024687/2500000000 : ℝ)|^8291 ≤ (13291609612577/100000000000000 : ℝ)^6243
        have hw : |(-547024687/2500000000 : ℝ)|=(547024687/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2696935221/5000000000 : ℝ)|^8291 ≤ (22025266457711/50000000000000 : ℝ)^6243
        have hw : |(2696935221/5000000000 : ℝ)|=(2696935221/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264956233/10000000000 : ℝ)|^8291 ≤ (42657857465063/100000000000000 : ℝ)^6243
        have hw : |(5264956233/10000000000 : ℝ)|=(5264956233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1098_s7_1 (p : ℝ) (hpa : (4145/1024 : ℝ) ≤ p) (hpb : p ≤ (8291/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (534491579/1000000000 : ℝ)*x 0 + (-70421823/312500000 : ℝ)*x 1 + (2632478157/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534491579/1000000000 : ℝ)^8291 ≤ (21760184675553/50000000000000 : ℝ)^6243 := by
    have hnat : (534491579 : ℕ)^8291*50000000000000^6243 ≤ 21760184675553^6243*1000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534491579 1000000000 21760184675553 50000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (70421823/312500000 : ℝ)^8291 ≤ (691088614743/5000000000000 : ℝ)^6243 := by
    have hnat : (70421823 : ℕ)^8291*5000000000000^6243 ≤ 691088614743^6243*312500000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      70421823 312500000 691088614743 5000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632478157/5000000000 : ℝ)^8291 ≤ (21328929168317/50000000000000 : ℝ)^6243 := by
    have hnat : (2632478157 : ℕ)^8291*50000000000000^6243 ≤ 21328929168317^6243*5000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632478157 5000000000 21328929168317 50000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8291/2048 : ℝ)) 8291 6243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(534491579/1000000000 : ℝ), (-70421823/312500000 : ℝ), (2632478157/5000000000 : ℝ)] ![(21760184675553/50000000000000 : ℝ), (691088614743/5000000000000 : ℝ), (21328929168317/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(534491579/1000000000 : ℝ)|^8291 ≤ (21760184675553/50000000000000 : ℝ)^6243
        have hw : |(534491579/1000000000 : ℝ)|=(534491579/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-70421823/312500000 : ℝ)|^8291 ≤ (691088614743/5000000000000 : ℝ)^6243
        have hw : |(-70421823/312500000 : ℝ)|=(70421823/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632478157/5000000000 : ℝ)|^8291 ≤ (21328929168317/50000000000000 : ℝ)^6243
        have hw : |(2632478157/5000000000 : ℝ)|=(2632478157/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1098_s7_2 (p : ℝ) (hpa : (4145/1024 : ℝ) ≤ p) (hpb : p ≤ (8291/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672457991/5000000000 : ℝ)*x 0 + (263247809/500000000 : ℝ)*x 1 + (-2253498259/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672457991/5000000000 : ℝ)^8291 ≤ (43520371427293/100000000000000 : ℝ)^6243 := by
    have hnat : (2672457991 : ℕ)^8291*100000000000000^6243 ≤ 43520371427293^6243*5000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672457991 5000000000 43520371427293 100000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (263247809/500000000 : ℝ)^8291 ≤ (1706314275791/4000000000000 : ℝ)^6243 := by
    have hnat : (263247809 : ℕ)^8291*4000000000000^6243 ≤ 1706314275791^6243*500000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263247809 500000000 1706314275791 4000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2253498259/10000000000 : ℝ)^8291 ≤ (6910885833827/50000000000000 : ℝ)^6243 := by
    have hnat : (2253498259 : ℕ)^8291*50000000000000^6243 ≤ 6910885833827^6243*10000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2253498259 10000000000 6910885833827 50000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8291/2048 : ℝ)) 8291 6243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672457991/5000000000 : ℝ), (263247809/500000000 : ℝ), (-2253498259/10000000000 : ℝ)] ![(43520371427293/100000000000000 : ℝ), (1706314275791/4000000000000 : ℝ), (6910885833827/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672457991/5000000000 : ℝ)|^8291 ≤ (43520371427293/100000000000000 : ℝ)^6243
        have hw : |(2672457991/5000000000 : ℝ)|=(2672457991/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(263247809/500000000 : ℝ)|^8291 ≤ (1706314275791/4000000000000 : ℝ)^6243
        have hw : |(263247809/500000000 : ℝ)|=(263247809/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2253498259/10000000000 : ℝ)|^8291 ≤ (6910885833827/50000000000000 : ℝ)^6243
        have hw : |(-2253498259/10000000000 : ℝ)|=(2253498259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1098_s7_3 (p : ℝ) (hpa : (4145/1024 : ℝ) ≤ p) (hpb : p ≤ (8291/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4370906459/10000000000 : ℝ)*x 0 + (2122817721/5000000000 : ℝ)*x 1 + (4499895067/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4370906459/10000000000 : ℝ)^8291 ≤ (33316696049781/100000000000000 : ℝ)^6243 := by
    have hnat : (4370906459 : ℕ)^8291*100000000000000^6243 ≤ 33316696049781^6243*10000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4370906459 10000000000 33316696049781 100000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2122817721/5000000000 : ℝ)^8291 ≤ (4006824109513/12500000000000 : ℝ)^6243 := by
    have hnat : (2122817721 : ℕ)^8291*12500000000000^6243 ≤ 4006824109513^6243*5000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2122817721 5000000000 4006824109513 12500000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4499895067/10000000000 : ℝ)^8291 ≤ (17314355528791/50000000000000 : ℝ)^6243 := by
    have hnat : (4499895067 : ℕ)^8291*50000000000000^6243 ≤ 17314355528791^6243*10000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4499895067 10000000000 17314355528791 50000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8291/2048 : ℝ)) 8291 6243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4370906459/10000000000 : ℝ), (2122817721/5000000000 : ℝ), (4499895067/10000000000 : ℝ)] ![(33316696049781/100000000000000 : ℝ), (4006824109513/12500000000000 : ℝ), (17314355528791/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4370906459/10000000000 : ℝ)|^8291 ≤ (33316696049781/100000000000000 : ℝ)^6243
        have hw : |(4370906459/10000000000 : ℝ)|=(4370906459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2122817721/5000000000 : ℝ)|^8291 ≤ (4006824109513/12500000000000 : ℝ)^6243
        have hw : |(2122817721/5000000000 : ℝ)|=(2122817721/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4499895067/10000000000 : ℝ)|^8291 ≤ (17314355528791/50000000000000 : ℝ)^6243
        have hw : |(4499895067/10000000000 : ℝ)|=(4499895067/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1098_s7_4 (p : ℝ) (hpa : (4145/1024 : ℝ) ≤ p) (hpb : p ≤ (8291/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-218810383/1000000000 : ℝ)*x 0 + (5265279891/10000000000 : ℝ)*x 1 + (1078709111/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (218810383/1000000000 : ℝ)^8291 ≤ (3322912652559/25000000000000 : ℝ)^6243 := by
    have hnat : (218810383 : ℕ)^8291*25000000000000^6243 ≤ 3322912652559^6243*1000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      218810383 1000000000 3322912652559 25000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265279891/10000000000 : ℝ)^8291 ≤ (42661340105023/100000000000000 : ℝ)^6243 := by
    have hnat : (5265279891 : ℕ)^8291*100000000000000^6243 ≤ 42661340105023^6243*10000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265279891 10000000000 42661340105023 100000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1078709111/2000000000 : ℝ)^8291 ≤ (5505876158669/12500000000000 : ℝ)^6243 := by
    have hnat : (1078709111 : ℕ)^8291*12500000000000^6243 ≤ 5505876158669^6243*2000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078709111 2000000000 5505876158669 12500000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8291/2048 : ℝ)) 8291 6243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-218810383/1000000000 : ℝ), (5265279891/10000000000 : ℝ), (1078709111/2000000000 : ℝ)] ![(3322912652559/25000000000000 : ℝ), (42661340105023/100000000000000 : ℝ), (5505876158669/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-218810383/1000000000 : ℝ)|^8291 ≤ (3322912652559/25000000000000 : ℝ)^6243
        have hw : |(-218810383/1000000000 : ℝ)|=(218810383/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265279891/10000000000 : ℝ)|^8291 ≤ (42661340105023/100000000000000 : ℝ)^6243
        have hw : |(5265279891/10000000000 : ℝ)|=(5265279891/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1078709111/2000000000 : ℝ)|^8291 ≤ (5505876158669/12500000000000 : ℝ)^6243
        have hw : |(1078709111/2000000000 : ℝ)|=(1078709111/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1098_s7_5 (p : ℝ) (hpa : (4145/1024 : ℝ) ≤ p) (hpb : p ≤ (8291/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (531236331/1000000000 : ℝ)*x 0 + (-531227269/2500000000 : ℝ)*x 1 + (5393545553/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (531236331/1000000000 : ℝ)^8291 ≤ (1726748641603/4000000000000 : ℝ)^6243 := by
    have hnat : (531236331 : ℕ)^8291*4000000000000^6243 ≤ 1726748641603^6243*1000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      531236331 1000000000 1726748641603 4000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (531227269/2500000000 : ℝ)^8291 ≤ (12784274700231/100000000000000 : ℝ)^6243 := by
    have hnat : (531227269 : ℕ)^8291*100000000000000^6243 ≤ 12784274700231^6243*2500000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      531227269 2500000000 12784274700231 100000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5393545553/10000000000 : ℝ)^8291 ≤ (44047009247661/100000000000000 : ℝ)^6243 := by
    have hnat : (5393545553 : ℕ)^8291*100000000000000^6243 ≤ 44047009247661^6243*10000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393545553 10000000000 44047009247661 100000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8291/2048 : ℝ)) 8291 6243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(531236331/1000000000 : ℝ), (-531227269/2500000000 : ℝ), (5393545553/10000000000 : ℝ)] ![(1726748641603/4000000000000 : ℝ), (12784274700231/100000000000000 : ℝ), (44047009247661/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(531236331/1000000000 : ℝ)|^8291 ≤ (1726748641603/4000000000000 : ℝ)^6243
        have hw : |(531236331/1000000000 : ℝ)|=(531236331/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-531227269/2500000000 : ℝ)|^8291 ≤ (12784274700231/100000000000000 : ℝ)^6243
        have hw : |(-531227269/2500000000 : ℝ)|=(531227269/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5393545553/10000000000 : ℝ)|^8291 ≤ (44047009247661/100000000000000 : ℝ)^6243
        have hw : |(5393545553/10000000000 : ℝ)|=(5393545553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1098_s7_6 (p : ℝ) (hpa : (4145/1024 : ℝ) ≤ p) (hpb : p ≤ (8291/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312363313/10000000000 : ℝ)*x 0 + (5393545551/10000000000 : ℝ)*x 1 + (-1062454537/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312363313/10000000000 : ℝ)^8291 ≤ (863374321449/2000000000000 : ℝ)^6243 := by
    have hnat : (5312363313 : ℕ)^8291*2000000000000^6243 ≤ 863374321449^6243*10000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312363313 10000000000 863374321449 2000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5393545551/10000000000 : ℝ)^8291 ≤ (4404700922597/10000000000000 : ℝ)^6243 := by
    have hnat : (5393545551 : ℕ)^8291*10000000000000^6243 ≤ 4404700922597^6243*10000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393545551 10000000000 4404700922597 10000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1062454537/5000000000 : ℝ)^8291 ≤ (12784274684251/100000000000000 : ℝ)^6243 := by
    have hnat : (1062454537 : ℕ)^8291*100000000000000^6243 ≤ 12784274684251^6243*5000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062454537 5000000000 12784274684251 100000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8291/2048 : ℝ)) 8291 6243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312363313/10000000000 : ℝ), (5393545551/10000000000 : ℝ), (-1062454537/5000000000 : ℝ)] ![(863374321449/2000000000000 : ℝ), (4404700922597/10000000000000 : ℝ), (12784274684251/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312363313/10000000000 : ℝ)|^8291 ≤ (863374321449/2000000000000 : ℝ)^6243
        have hw : |(5312363313/10000000000 : ℝ)|=(5312363313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5393545551/10000000000 : ℝ)|^8291 ≤ (4404700922597/10000000000000 : ℝ)^6243
        have hw : |(5393545551/10000000000 : ℝ)|=(5393545551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1062454537/5000000000 : ℝ)|^8291 ≤ (12784274684251/100000000000000 : ℝ)^6243
        have hw : |(-1062454537/5000000000 : ℝ)|=(1062454537/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1098_s7_7 (p : ℝ) (hpa : (4145/1024 : ℝ) ≤ p) (hpb : p ≤ (8291/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4370916259/10000000000 : ℝ)*x 0 + (8787611/19531250 : ℝ)*x 1 + (2123138023/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4370916259/10000000000 : ℝ)^8291 ≤ (1665839762701/5000000000000 : ℝ)^6243 := by
    have hnat : (4370916259 : ℕ)^8291*5000000000000^6243 ≤ 1665839762701^6243*10000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4370916259 10000000000 1665839762701 5000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8787611/19531250 : ℝ)^8291 ≤ (34622188498329/100000000000000 : ℝ)^6243 := by
    have hnat : (8787611 : ℕ)^8291*100000000000000^6243 ≤ 34622188498329^6243*19531250^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8787611 19531250 34622188498329 100000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2123138023/5000000000 : ℝ)^8291 ≤ (32061016225401/100000000000000 : ℝ)^6243 := by
    have hnat : (2123138023 : ℕ)^8291*100000000000000^6243 ≤ 32061016225401^6243*5000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2123138023 5000000000 32061016225401 100000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8291/2048 : ℝ)) 8291 6243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4370916259/10000000000 : ℝ), (8787611/19531250 : ℝ), (2123138023/5000000000 : ℝ)] ![(1665839762701/5000000000000 : ℝ), (34622188498329/100000000000000 : ℝ), (32061016225401/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4370916259/10000000000 : ℝ)|^8291 ≤ (1665839762701/5000000000000 : ℝ)^6243
        have hw : |(4370916259/10000000000 : ℝ)|=(4370916259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(8787611/19531250 : ℝ)|^8291 ≤ (34622188498329/100000000000000 : ℝ)^6243
        have hw : |(8787611/19531250 : ℝ)|=(8787611/19531250 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2123138023/5000000000 : ℝ)|^8291 ≤ (32061016225401/100000000000000 : ℝ)^6243
        have hw : |(2123138023/5000000000 : ℝ)|=(2123138023/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1098_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4145/1024 : ℝ) ≤ p) (hpb : p ≤ (8291/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148615943/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14033/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5643/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (5647/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1753/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14033/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5643/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14033/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5643/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14033/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5643/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14033/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5643/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14033/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5643/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14033/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5643/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5643/50000 : ℝ) ^ (4145/1024 : ℝ) ≤ (3653951286857617/25000000000000000000 : ℝ) := by
    have hpowers : (5643/50000 : ℝ)^4145 ≤ (3653951286857617/25000000000000000000 : ℝ)^1024 := by
      have hnat : (5643 : ℕ)^4145*25000000000000000000^1024 ≤ 3653951286857617^1024*50000^4145 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5643 50000 3653951286857617 25000000000000000000 4145 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5643/50000 : ℝ)) (X := (3653951286857617/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4145 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14033/100000 : ℝ) ^ (4145/1024 : ℝ) ≤ (17650699662841957/50000000000000000000 : ℝ) := by
    have hpowers : (14033/100000 : ℝ)^4145 ≤ (17650699662841957/50000000000000000000 : ℝ)^1024 := by
      have hnat : (14033 : ℕ)^4145*50000000000000000000^1024 ≤ 17650699662841957^1024*100000^4145 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14033 100000 17650699662841957 50000000000000000000 4145 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14033/100000 : ℝ)) (X := (17650699662841957/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4145 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12503653951286857617/12500000000000000000 : ℝ) ≤ (2000144414356307/2000000000000000 : ℝ) ^ (4145/1024 : ℝ) := by
    have hpowers : (12503653951286857617/12500000000000000000 : ℝ)^1024 ≤ (2000144414356307/2000000000000000 : ℝ)^4145 := by
      have hnat : (12503653951286857617 : ℕ)^1024*2000000000000000^4145 ≤ 2000144414356307^4145*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12503653951286857617 12500000000000000000 2000144414356307 2000000000000000 1024 4145 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000144414356307/2000000000000000 : ℝ)) (X := (12503653951286857617/12500000000000000000 : ℝ)) (by norm_num) 4145 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50024958602236557191/50000000000000000000 : ℝ) ≤ (10001232946061399/10000000000000000 : ℝ) ^ (4145/1024 : ℝ) := by
    have hpowers : (50024958602236557191/50000000000000000000 : ℝ)^1024 ≤ (10001232946061399/10000000000000000 : ℝ)^4145 := by
      have hnat : (50024958602236557191 : ℕ)^1024*10000000000000000^4145 ≤ 10001232946061399^4145*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50024958602236557191 50000000000000000000 10001232946061399 10000000000000000 1024 4145 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001232946061399/10000000000000000 : ℝ)) (X := (50024958602236557191/50000000000000000000 : ℝ)) (by norm_num) 4145 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25017650699662841957/25000000000000000000 : ℝ) ≤ (10001743820341263/10000000000000000 : ℝ) ^ (4145/1024 : ℝ) := by
    have hpowers : (25017650699662841957/25000000000000000000 : ℝ)^1024 ≤ (10001743820341263/10000000000000000 : ℝ)^4145 := by
      have hnat : (25017650699662841957 : ℕ)^1024*10000000000000000^4145 ≤ 10001743820341263^4145*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25017650699662841957 25000000000000000000 10001743820341263 10000000000000000 1024 4145 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001743820341263/10000000000000000 : ℝ)) (X := (25017650699662841957/25000000000000000000 : ℝ)) (by norm_num) 4145 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3653951286857617/25000000000000000000 : ℝ) ≤ ((27460452076938786437/27470000000000000000 : ℝ)+2*(63859284983/34337500000000 : ℝ)*(5643/50000 : ℝ))^(4145/1024 : ℝ) := by
    rw [show (27460452076938786437/27470000000000000000 : ℝ)+2*(63859284983/34337500000000 : ℝ)*(5643/50000 : ℝ)=(2000144414356307/2000000000000000 : ℝ) by norm_num, show 1+2*(3653951286857617/25000000000000000000 : ℝ)=(12503653951286857617/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(17650699662841957/50000000000000000000 : ℝ)+(3653951286857617/25000000000000000000 : ℝ) ≤ ((27460452076938786437/27470000000000000000 : ℝ)+(63859284983/34337500000000 : ℝ)*((14033/100000 : ℝ)+(5643/50000 : ℝ)))^(4145/1024 : ℝ) := by
    rw [show (27460452076938786437/27470000000000000000 : ℝ)+(63859284983/34337500000000 : ℝ)*((14033/100000 : ℝ)+(5643/50000 : ℝ))=(10001232946061399/10000000000000000 : ℝ) by norm_num, show 1+(17650699662841957/50000000000000000000 : ℝ)+(3653951286857617/25000000000000000000 : ℝ)=(50024958602236557191/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(17650699662841957/50000000000000000000 : ℝ) ≤ ((27460452076938786437/27470000000000000000 : ℝ)+2*(63859284983/34337500000000 : ℝ)*(14033/100000 : ℝ))^(4145/1024 : ℝ) := by
    rw [show (27460452076938786437/27470000000000000000 : ℝ)+2*(63859284983/34337500000000 : ℝ)*(14033/100000 : ℝ)=(10001743820341263/10000000000000000 : ℝ) by norm_num, show 1+2*(17650699662841957/50000000000000000000 : ℝ)=(25017650699662841957/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (27460452076938786437/27470000000000000000 : ℝ)*(X 1 0+X 2 0)+(63859284983/34337500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4145/1024 : ℝ)) (lo := (5643/50000 : ℝ)) (hi := (14033/100000 : ℝ)) (c := (27460452076938786437/27470000000000000000 : ℝ)) (alpha := (63859284983/34337500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (27460452076938786437/27470000000000000000 : ℝ)*(X 0 1+X 2 1)+(63859284983/34337500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4145/1024 : ℝ)) (lo := (5643/50000 : ℝ)) (hi := (14033/100000 : ℝ)) (c := (27460452076938786437/27470000000000000000 : ℝ)) (alpha := (63859284983/34337500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (27460452076938786437/27470000000000000000 : ℝ)*(X 0 2+X 1 2)+(63859284983/34337500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4145/1024 : ℝ)) (lo := (5643/50000 : ℝ)) (hi := (14033/100000 : ℝ)) (c := (27460452076938786437/27470000000000000000 : ℝ)) (alpha := (63859284983/34337500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-547024687/2500000000 : ℝ)*X 0 0+(2696935221/5000000000 : ℝ)*X 0 1+(5264956233/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1098_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((534491579/1000000000 : ℝ)*X 1 0+(-70421823/312500000 : ℝ)*X 1 1+(2632478157/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1098_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672457991/5000000000 : ℝ)*X 2 0+(263247809/500000000 : ℝ)*X 2 1+(-2253498259/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1098_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4370906459/10000000000 : ℝ)*X 0 0+(2122817721/5000000000 : ℝ)*X 0 1+(4499895067/10000000000 : ℝ)*X 0 2+(4370906459/10000000000 : ℝ)*X 1 0+(2122817721/5000000000 : ℝ)*X 1 1+(4499895067/10000000000 : ℝ)*X 1 2+(4370906459/10000000000 : ℝ)*X 2 0+(2122817721/5000000000 : ℝ)*X 2 1+(4499895067/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1098_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-218810383/1000000000 : ℝ)*X 0 0+(5265279891/10000000000 : ℝ)*X 0 1+(1078709111/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1098_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((531236331/1000000000 : ℝ)*X 1 0+(-531227269/2500000000 : ℝ)*X 1 1+(5393545553/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1098_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312363313/10000000000 : ℝ)*X 2 0+(5393545551/10000000000 : ℝ)*X 2 1+(-1062454537/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1098_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4370916259/10000000000 : ℝ)*X 0 0+(8787611/19531250 : ℝ)*X 0 1+(2123138023/5000000000 : ℝ)*X 0 2+(4370916259/10000000000 : ℝ)*X 1 0+(8787611/19531250 : ℝ)*X 1 1+(2123138023/5000000000 : ℝ)*X 1 2+(4370916259/10000000000 : ℝ)*X 2 0+(8787611/19531250 : ℝ)*X 2 1+(2123138023/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1098_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4152190785757213416672307467/1373500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (138657623/20000000000000 : ℝ)*(base19) + (95414903/12500000000000 : ℝ)*(base23) + (111506141/100000000000000 : ℝ)*(lower2) + (31256307/100000000000000 : ℝ)*(upper3) + (12848099/25000000000000 : ℝ)*(upper5) + (5845076803851397/100000000000000 : ℝ)*(major0) + (5845076803851397/100000000000000 : ℝ)*(major1) + (5845076803851397/100000000000000 : ℝ)*(major2) + (7757117605553253/100000000000000 : ℝ)*(sp0) + (7757144896822409/100000000000000 : ℝ)*(sp1) + (77571448267913/1000000000000 : ℝ)*(sp2) + (983249183781953/25000000000000 : ℝ)*(sp3) + (2798455727/10000000000000 : ℝ)*(sp4) + (11181695349/100000000000000 : ℝ)*(sp7) + (1966503958411581/50000000000000 : ℝ)*(f.failure) + (1939286397527631/25000000000000 : ℝ)*(f.sum) + (2967723425083/13735000000000000000000000000 : ℝ)*base65 + (14723266149128097511/2747000000000000000000000000000000 : ℝ)*base68 + (7971226924111097511/2747000000000000000000000000000000 : ℝ)*base70 + (3626522050744902489/2747000000000000000000000000000000 : ℝ)*base71 + (227649029723/214609375000000000000000000 : ℝ)*base74 + (9186453690519902489/2747000000000000000000000000000000 : ℝ)*base75 + (41585302941285097511/2747000000000000000000000000000000 : ℝ)*base78 + (30718301624316097511/2747000000000000000000000000000000 : ℝ)*base80 + (41705978224439/6867500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (42435883/5000000000000000000000 : ℝ)*base89 + (42435883/5000000000000000000000 : ℝ)*base91 + (42435883/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (624215465369029717557542733/171687500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (13177397/2000000000000 : ℝ)*(base19) + (90724717/12500000000000 : ℝ)*(base23) + (70934273/100000000000000 : ℝ)*(upper3) + (2815277/10000000000000 : ℝ)*(lower4) + (14623839/20000000000000 : ℝ)*(upper5) + (734324214081803/12500000000000 : ℝ)*(major0) + (734324214081803/12500000000000 : ℝ)*(major1) + (734324214081803/12500000000000 : ℝ)*(major2) + (3593020041/20000000000000 : ℝ)*(sp1) + (19520278891/100000000000000 : ℝ)*(sp2) + (7796318187877613/100000000000000 : ℝ)*(sp4) + (7796299563907559/100000000000000 : ℝ)*(sp5) + (1559259588360197/20000000000000 : ℝ)*(sp6) + (1976434558119523/50000000000000 : ℝ)*(sp7) + (1976434558119523/50000000000000 : ℝ)*(f.failure) + (7796318187877613/100000000000000 : ℝ)*(f.sum) + (7263655782549/3433750000000000000000000000 : ℝ)*base65 + (2013022565058480911/343375000000000000000000000000000 : ℝ)*base67 + (3048534351113019089/343375000000000000000000000000000 : ℝ)*base70 + (780093967585644089/343375000000000000000000000000000 : ℝ)*base72 + (10455547637011/3433750000000000000000000000 : ℝ)*base74 + (11847456672069769089/343375000000000000000000000000000 : ℝ)*base76 + (3583545513606769089/343375000000000000000000000000000 : ℝ)*base78 + (3259410657407980911/343375000000000000000000000000000 : ℝ)*base79 + (41441807263559/13735000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base88 + (17355189/5000000000000000000000 : ℝ)*base89 + (17355189/5000000000000000000000 : ℝ)*base91 + (17355189/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1098_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4145/1024 : ℝ) ≤ p) (hpb : p ≤ (8291/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148615943/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14033/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5643/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5647/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1753/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1098_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1098_s8_0 (p : ℝ) (hpa : (4145/1024 : ℝ) ≤ p) (hpb : p ≤ (8291/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2188108731/10000000000 : ℝ)*x 0 + (2696890457/5000000000 : ℝ)*x 1 + (5265038989/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2188108731/10000000000 : ℝ)^8291 ≤ (13291690147757/100000000000000 : ℝ)^6243 := by
    have hnat : (2188108731 : ℕ)^8291*100000000000000^6243 ≤ 13291690147757^6243*10000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2188108731 10000000000 13291690147757 100000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2696890457/5000000000 : ℝ)^8291 ≤ (4404956190937/10000000000000 : ℝ)^6243 := by
    have hnat : (2696890457 : ℕ)^8291*10000000000000^6243 ≤ 4404956190937^6243*5000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696890457 5000000000 4404956190937 10000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265038989/10000000000 : ℝ)^8291 ≤ (10664686983341/25000000000000 : ℝ)^6243 := by
    have hnat : (5265038989 : ℕ)^8291*25000000000000^6243 ≤ 10664686983341^6243*10000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265038989 10000000000 10664686983341 25000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8291/2048 : ℝ)) 8291 6243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2188108731/10000000000 : ℝ), (2696890457/5000000000 : ℝ), (5265038989/10000000000 : ℝ)] ![(13291690147757/100000000000000 : ℝ), (4404956190937/10000000000000 : ℝ), (10664686983341/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2188108731/10000000000 : ℝ)|^8291 ≤ (13291690147757/100000000000000 : ℝ)^6243
        have hw : |(-2188108731/10000000000 : ℝ)|=(2188108731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2696890457/5000000000 : ℝ)|^8291 ≤ (4404956190937/10000000000000 : ℝ)^6243
        have hw : |(2696890457/5000000000 : ℝ)|=(2696890457/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265038989/10000000000 : ℝ)|^8291 ≤ (10664686983341/25000000000000 : ℝ)^6243
        have hw : |(5265038989/10000000000 : ℝ)|=(5265038989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1098_s8_1 (p : ℝ) (hpa : (4145/1024 : ℝ) ≤ p) (hpb : p ≤ (8291/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344892671/10000000000 : ℝ)*x 0 + (-2253418981/10000000000 : ℝ)*x 1 + (263251981/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344892671/10000000000 : ℝ)^8291 ≤ (5440014919319/12500000000000 : ℝ)^6243 := by
    have hnat : (5344892671 : ℕ)^8291*12500000000000^6243 ≤ 5440014919319^6243*10000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344892671 10000000000 5440014919319 12500000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2253418981/10000000000 : ℝ)^8291 ≤ (6910562954491/50000000000000 : ℝ)^6243 := by
    have hnat : (2253418981 : ℕ)^8291*50000000000000^6243 ≤ 6910562954491^6243*10000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2253418981 10000000000 6910562954491 50000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (263251981/500000000 : ℝ)^8291 ≤ (42658754723047/100000000000000 : ℝ)^6243 := by
    have hnat : (263251981 : ℕ)^8291*100000000000000^6243 ≤ 42658754723047^6243*500000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263251981 500000000 42658754723047 100000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8291/2048 : ℝ)) 8291 6243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344892671/10000000000 : ℝ), (-2253418981/10000000000 : ℝ), (263251981/500000000 : ℝ)] ![(5440014919319/12500000000000 : ℝ), (6910562954491/50000000000000 : ℝ), (42658754723047/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344892671/10000000000 : ℝ)|^8291 ≤ (5440014919319/12500000000000 : ℝ)^6243
        have hw : |(5344892671/10000000000 : ℝ)|=(5344892671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2253418981/10000000000 : ℝ)|^8291 ≤ (6910562954491/50000000000000 : ℝ)^6243
        have hw : |(-2253418981/10000000000 : ℝ)|=(2253418981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(263251981/500000000 : ℝ)|^8291 ≤ (42658754723047/100000000000000 : ℝ)^6243
        have hw : |(263251981/500000000 : ℝ)|=(263251981/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1098_s8_2 (p : ℝ) (hpa : (4145/1024 : ℝ) ≤ p) (hpb : p ≤ (8291/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672446139/5000000000 : ℝ)*x 0 + (5265040127/10000000000 : ℝ)*x 1 + (-140838677/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672446139/5000000000 : ℝ)^8291 ≤ (21760057552431/50000000000000 : ℝ)^6243 := by
    have hnat : (2672446139 : ℕ)^8291*50000000000000^6243 ≤ 21760057552431^6243*5000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672446139 5000000000 21760057552431 50000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265040127/10000000000 : ℝ)^8291 ≤ (8531752035693/20000000000000 : ℝ)^6243 := by
    have hnat : (5265040127 : ℕ)^8291*20000000000000^6243 ≤ 8531752035693^6243*10000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265040127 10000000000 8531752035693 20000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (140838677/625000000 : ℝ)^8291 ≤ (1382112469531/10000000000000 : ℝ)^6243 := by
    have hnat : (140838677 : ℕ)^8291*10000000000000^6243 ≤ 1382112469531^6243*625000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      140838677 625000000 1382112469531 10000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8291/2048 : ℝ)) 8291 6243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672446139/5000000000 : ℝ), (5265040127/10000000000 : ℝ), (-140838677/625000000 : ℝ)] ![(21760057552431/50000000000000 : ℝ), (8531752035693/20000000000000 : ℝ), (1382112469531/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672446139/5000000000 : ℝ)|^8291 ≤ (21760057552431/50000000000000 : ℝ)^6243
        have hw : |(2672446139/5000000000 : ℝ)|=(2672446139/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265040127/10000000000 : ℝ)|^8291 ≤ (8531752035693/20000000000000 : ℝ)^6243
        have hw : |(5265040127/10000000000 : ℝ)|=(5265040127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-140838677/625000000 : ℝ)|^8291 ≤ (1382112469531/10000000000000 : ℝ)^6243
        have hw : |(-140838677/625000000 : ℝ)|=(140838677/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1098_s8_3 (p : ℝ) (hpa : (4145/1024 : ℝ) ≤ p) (hpb : p ≤ (8291/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2185455527/5000000000 : ℝ)*x 0 + (4245804789/10000000000 : ℝ)*x 1 + (4499724367/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2185455527/5000000000 : ℝ)^8291 ≤ (33316742564413/100000000000000 : ℝ)^6243 := by
    have hnat : (2185455527 : ℕ)^8291*100000000000000^6243 ≤ 33316742564413^6243*5000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2185455527 5000000000 33316742564413 100000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4245804789/10000000000 : ℝ)^8291 ≤ (16028145445497/50000000000000 : ℝ)^6243 := by
    have hnat : (4245804789 : ℕ)^8291*50000000000000^6243 ≤ 16028145445497^6243*10000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4245804789 10000000000 16028145445497 50000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4499724367/10000000000 : ℝ)^8291 ≤ (34626966527997/100000000000000 : ℝ)^6243 := by
    have hnat : (4499724367 : ℕ)^8291*100000000000000^6243 ≤ 34626966527997^6243*10000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4499724367 10000000000 34626966527997 100000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8291/2048 : ℝ)) 8291 6243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2185455527/5000000000 : ℝ), (4245804789/10000000000 : ℝ), (4499724367/10000000000 : ℝ)] ![(33316742564413/100000000000000 : ℝ), (16028145445497/50000000000000 : ℝ), (34626966527997/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2185455527/5000000000 : ℝ)|^8291 ≤ (33316742564413/100000000000000 : ℝ)^6243
        have hw : |(2185455527/5000000000 : ℝ)|=(2185455527/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4245804789/10000000000 : ℝ)|^8291 ≤ (16028145445497/50000000000000 : ℝ)^6243
        have hw : |(4245804789/10000000000 : ℝ)|=(4245804789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4499724367/10000000000 : ℝ)|^8291 ≤ (34626966527997/100000000000000 : ℝ)^6243
        have hw : |(4499724367/10000000000 : ℝ)|=(4499724367/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1098_s8_4 (p : ℝ) (hpa : (4145/1024 : ℝ) ≤ p) (hpb : p ≤ (8291/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1094056787/5000000000 : ℝ)*x 0 + (5265362221/10000000000 : ℝ)*x 1 + (337091039/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1094056787/5000000000 : ℝ)^8291 ≤ (13291729217407/100000000000000 : ℝ)^6243 := by
    have hnat : (1094056787 : ℕ)^8291*100000000000000^6243 ≤ 13291729217407^6243*5000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1094056787 5000000000 13291729217407 100000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265362221/10000000000 : ℝ)^8291 ≤ (21331113003673/50000000000000 : ℝ)^6243 := by
    have hnat : (5265362221 : ℕ)^8291*50000000000000^6243 ≤ 21331113003673^6243*10000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265362221 10000000000 21331113003673 50000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (337091039/625000000 : ℝ)^8291 ≤ (22023022378653/50000000000000 : ℝ)^6243 := by
    have hnat : (337091039 : ℕ)^8291*50000000000000^6243 ≤ 22023022378653^6243*625000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337091039 625000000 22023022378653 50000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8291/2048 : ℝ)) 8291 6243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1094056787/5000000000 : ℝ), (5265362221/10000000000 : ℝ), (337091039/625000000 : ℝ)] ![(13291729217407/100000000000000 : ℝ), (21331113003673/50000000000000 : ℝ), (22023022378653/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1094056787/5000000000 : ℝ)|^8291 ≤ (13291729217407/100000000000000 : ℝ)^6243
        have hw : |(-1094056787/5000000000 : ℝ)|=(1094056787/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265362221/10000000000 : ℝ)|^8291 ≤ (21331113003673/50000000000000 : ℝ)^6243
        have hw : |(5265362221/10000000000 : ℝ)|=(5265362221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(337091039/625000000 : ℝ)|^8291 ≤ (22023022378653/50000000000000 : ℝ)^6243
        have hw : |(337091039/625000000 : ℝ)|=(337091039/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1098_s8_5 (p : ℝ) (hpa : (4145/1024 : ℝ) ≤ p) (hpb : p ≤ (8291/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1328096007/2500000000 : ℝ)*x 0 + (-2125001809/10000000000 : ℝ)*x 1 + (269672831/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328096007/2500000000 : ℝ)^8291 ≤ (21584469812637/50000000000000 : ℝ)^6243 := by
    have hnat : (1328096007 : ℕ)^8291*50000000000000^6243 ≤ 21584469812637^6243*2500000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328096007 2500000000 21584469812637 50000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2125001809/10000000000 : ℝ)^8291 ≤ (12785015646543/100000000000000 : ℝ)^6243 := by
    have hnat : (2125001809 : ℕ)^8291*100000000000000^6243 ≤ 12785015646543^6243*10000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2125001809 10000000000 12785015646543 100000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (269672831/500000000 : ℝ)^8291 ≤ (11011511178481/25000000000000 : ℝ)^6243 := by
    have hnat : (269672831 : ℕ)^8291*25000000000000^6243 ≤ 11011511178481^6243*500000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269672831 500000000 11011511178481 25000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8291/2048 : ℝ)) 8291 6243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1328096007/2500000000 : ℝ), (-2125001809/10000000000 : ℝ), (269672831/500000000 : ℝ)] ![(21584469812637/50000000000000 : ℝ), (12785015646543/100000000000000 : ℝ), (11011511178481/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1328096007/2500000000 : ℝ)|^8291 ≤ (21584469812637/50000000000000 : ℝ)^6243
        have hw : |(1328096007/2500000000 : ℝ)|=(1328096007/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2125001809/10000000000 : ℝ)|^8291 ≤ (12785015646543/100000000000000 : ℝ)^6243
        have hw : |(-2125001809/10000000000 : ℝ)|=(2125001809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(269672831/500000000 : ℝ)|^8291 ≤ (11011511178481/25000000000000 : ℝ)^6243
        have hw : |(269672831/500000000 : ℝ)|=(269672831/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1098_s8_6 (p : ℝ) (hpa : (4145/1024 : ℝ) ≤ p) (hpb : p ≤ (8291/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312383889/10000000000 : ℝ)*x 0 + (2696728379/5000000000 : ℝ)*x 1 + (-2125001809/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312383889/10000000000 : ℝ)^8291 ≤ (5396117265651/12500000000000 : ℝ)^6243 := by
    have hnat : (5312383889 : ℕ)^8291*12500000000000^6243 ≤ 5396117265651^6243*10000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312383889 10000000000 5396117265651 12500000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2696728379/5000000000 : ℝ)^8291 ≤ (5505755776327/12500000000000 : ℝ)^6243 := by
    have hnat : (2696728379 : ℕ)^8291*12500000000000^6243 ≤ 5505755776327^6243*5000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696728379 5000000000 5505755776327 12500000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2125001809/10000000000 : ℝ)^8291 ≤ (12785015646543/100000000000000 : ℝ)^6243 := by
    have hnat : (2125001809 : ℕ)^8291*100000000000000^6243 ≤ 12785015646543^6243*10000000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2125001809 10000000000 12785015646543 100000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8291/2048 : ℝ)) 8291 6243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312383889/10000000000 : ℝ), (2696728379/5000000000 : ℝ), (-2125001809/10000000000 : ℝ)] ![(5396117265651/12500000000000 : ℝ), (5505755776327/12500000000000 : ℝ), (12785015646543/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312383889/10000000000 : ℝ)|^8291 ≤ (5396117265651/12500000000000 : ℝ)^6243
        have hw : |(5312383889/10000000000 : ℝ)|=(5312383889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2696728379/5000000000 : ℝ)|^8291 ≤ (5505755776327/12500000000000 : ℝ)^6243
        have hw : |(2696728379/5000000000 : ℝ)|=(2696728379/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2125001809/10000000000 : ℝ)|^8291 ≤ (12785015646543/100000000000000 : ℝ)^6243
        have hw : |(-2125001809/10000000000 : ℝ)|=(2125001809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1098_s8_7 (p : ℝ) (hpa : (4145/1024 : ℝ) ≤ p) (hpb : p ≤ (8291/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (546365069/1250000000 : ℝ)*x 0 + (562385939/1250000000 : ℝ)*x 1 + (1061611069/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (546365069/1250000000 : ℝ)^8291 ≤ (16658419355787/50000000000000 : ℝ)^6243 := by
    have hnat : (546365069 : ℕ)^8291*50000000000000^6243 ≤ 16658419355787^6243*1250000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      546365069 1250000000 16658419355787 50000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (562385939/1250000000 : ℝ)^8291 ≤ (17310229076289/50000000000000 : ℝ)^6243 := by
    have hnat : (562385939 : ℕ)^8291*50000000000000^6243 ≤ 17310229076289^6243*1250000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      562385939 1250000000 17310229076289 50000000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1061611069/2500000000 : ℝ)^8291 ≤ (2003918945233/6250000000000 : ℝ)^6243 := by
    have hnat : (1061611069 : ℕ)^8291*6250000000000^6243 ≤ 2003918945233^6243*2500000000^8291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061611069 2500000000 2003918945233 6250000000000 8291 6243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8291/2048 : ℝ)) 8291 6243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(546365069/1250000000 : ℝ), (562385939/1250000000 : ℝ), (1061611069/2500000000 : ℝ)] ![(16658419355787/50000000000000 : ℝ), (17310229076289/50000000000000 : ℝ), (2003918945233/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(546365069/1250000000 : ℝ)|^8291 ≤ (16658419355787/50000000000000 : ℝ)^6243
        have hw : |(546365069/1250000000 : ℝ)|=(546365069/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(562385939/1250000000 : ℝ)|^8291 ≤ (17310229076289/50000000000000 : ℝ)^6243
        have hw : |(562385939/1250000000 : ℝ)|=(562385939/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1061611069/2500000000 : ℝ)|^8291 ≤ (2003918945233/6250000000000 : ℝ)^6243
        have hw : |(1061611069/2500000000 : ℝ)|=(1061611069/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1098_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4145/1024 : ℝ) ≤ p) (hpb : p ≤ (8291/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148615943/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1753/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5647/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (2259/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7011/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1753/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5647/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1753/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5647/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1753/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5647/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1753/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5647/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1753/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5647/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1753/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5647/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5647/50000 : ℝ) ^ (4145/1024 : ℝ) ≤ (14657787461443461/100000000000000000000 : ℝ) := by
    have hpowers : (5647/50000 : ℝ)^4145 ≤ (14657787461443461/100000000000000000000 : ℝ)^1024 := by
      have hnat : (5647 : ℕ)^4145*100000000000000000000^1024 ≤ 14657787461443461^1024*50000^4145 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5647 50000 14657787461443461 100000000000000000000 4145 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5647/50000 : ℝ)) (X := (14657787461443461/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4145 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1753/12500 : ℝ) ^ (4145/1024 : ℝ) ≤ (7041968783697323/20000000000000000000 : ℝ) := by
    have hpowers : (1753/12500 : ℝ)^4145 ≤ (7041968783697323/20000000000000000000 : ℝ)^1024 := by
      have hnat : (1753 : ℕ)^4145*20000000000000000000^1024 ≤ 7041968783697323^1024*12500^4145 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1753 12500 7041968783697323 20000000000000000000 4145 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1753/12500 : ℝ)) (X := (7041968783697323/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4145 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014657787461443461/50000000000000000000 : ℝ) ≤ (2000144829125101/2000000000000000 : ℝ) ^ (4145/1024 : ℝ) := by
    have hpowers : (50014657787461443461/50000000000000000000 : ℝ)^1024 ≤ (2000144829125101/2000000000000000 : ℝ)^4145 := by
      have hnat : (50014657787461443461 : ℕ)^1024*2000000000000000^4145 ≤ 2000144829125101^4145*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014657787461443461 50000000000000000000 2000144829125101 2000000000000000 1024 4145 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000144829125101/2000000000000000 : ℝ)) (X := (50014657787461443461/50000000000000000000 : ℝ)) (by norm_num) 4145 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25012466907844982519/25000000000000000000 : ℝ) ≤ (2500307930461153/2500000000000000 : ℝ) ^ (4145/1024 : ℝ) := by
    have hpowers : (25012466907844982519/25000000000000000000 : ℝ)^1024 ≤ (2500307930461153/2500000000000000 : ℝ)^4145 := by
      have hnat : (25012466907844982519 : ℕ)^1024*2500000000000000^4145 ≤ 2500307930461153^4145*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25012466907844982519 25000000000000000000 2500307930461153 2500000000000000 1024 4145 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500307930461153/2500000000000000 : ℝ)) (X := (25012466907844982519/25000000000000000000 : ℝ)) (by norm_num) 4145 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10007041968783697323/10000000000000000000 : ℝ) ≤ (10001739298063719/10000000000000000 : ℝ) ^ (4145/1024 : ℝ) := by
    have hpowers : (10007041968783697323/10000000000000000000 : ℝ)^1024 ≤ (10001739298063719/10000000000000000 : ℝ)^4145 := by
      have hnat : (10007041968783697323 : ℕ)^1024*10000000000000000^4145 ≤ 10001739298063719^4145*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10007041968783697323 10000000000000000000 10001739298063719 10000000000000000 1024 4145 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001739298063719/10000000000000000 : ℝ)) (X := (10007041968783697323/10000000000000000000 : ℝ)) (by norm_num) 4145 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14657787461443461/100000000000000000000 : ℝ) ≤ ((13645255892960219867/13650000000000000000 : ℝ)+2*(507576219107/273000000000000 : ℝ)*(5647/50000 : ℝ))^(4145/1024 : ℝ) := by
    rw [show (13645255892960219867/13650000000000000000 : ℝ)+2*(507576219107/273000000000000 : ℝ)*(5647/50000 : ℝ)=(2000144829125101/2000000000000000 : ℝ) by norm_num, show 1+2*(14657787461443461/100000000000000000000 : ℝ)=(50014657787461443461/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(7041968783697323/20000000000000000000 : ℝ)+(14657787461443461/100000000000000000000 : ℝ) ≤ ((13645255892960219867/13650000000000000000 : ℝ)+(507576219107/273000000000000 : ℝ)*((1753/12500 : ℝ)+(5647/50000 : ℝ)))^(4145/1024 : ℝ) := by
    rw [show (13645255892960219867/13650000000000000000 : ℝ)+(507576219107/273000000000000 : ℝ)*((1753/12500 : ℝ)+(5647/50000 : ℝ))=(2500307930461153/2500000000000000 : ℝ) by norm_num, show 1+(7041968783697323/20000000000000000000 : ℝ)+(14657787461443461/100000000000000000000 : ℝ)=(25012466907844982519/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(7041968783697323/20000000000000000000 : ℝ) ≤ ((13645255892960219867/13650000000000000000 : ℝ)+2*(507576219107/273000000000000 : ℝ)*(1753/12500 : ℝ))^(4145/1024 : ℝ) := by
    rw [show (13645255892960219867/13650000000000000000 : ℝ)+2*(507576219107/273000000000000 : ℝ)*(1753/12500 : ℝ)=(10001739298063719/10000000000000000 : ℝ) by norm_num, show 1+2*(7041968783697323/20000000000000000000 : ℝ)=(10007041968783697323/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13645255892960219867/13650000000000000000 : ℝ)*(X 1 0+X 2 0)+(507576219107/273000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4145/1024 : ℝ)) (lo := (5647/50000 : ℝ)) (hi := (1753/12500 : ℝ)) (c := (13645255892960219867/13650000000000000000 : ℝ)) (alpha := (507576219107/273000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13645255892960219867/13650000000000000000 : ℝ)*(X 0 1+X 2 1)+(507576219107/273000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4145/1024 : ℝ)) (lo := (5647/50000 : ℝ)) (hi := (1753/12500 : ℝ)) (c := (13645255892960219867/13650000000000000000 : ℝ)) (alpha := (507576219107/273000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13645255892960219867/13650000000000000000 : ℝ)*(X 0 2+X 1 2)+(507576219107/273000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4145/1024 : ℝ)) (lo := (5647/50000 : ℝ)) (hi := (1753/12500 : ℝ)) (c := (13645255892960219867/13650000000000000000 : ℝ)) (alpha := (507576219107/273000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2188108731/10000000000 : ℝ)*X 0 0+(2696890457/5000000000 : ℝ)*X 0 1+(5265038989/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1098_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344892671/10000000000 : ℝ)*X 1 0+(-2253418981/10000000000 : ℝ)*X 1 1+(263251981/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1098_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672446139/5000000000 : ℝ)*X 2 0+(5265040127/10000000000 : ℝ)*X 2 1+(-140838677/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1098_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2185455527/5000000000 : ℝ)*X 0 0+(4245804789/10000000000 : ℝ)*X 0 1+(4499724367/10000000000 : ℝ)*X 0 2+(2185455527/5000000000 : ℝ)*X 1 0+(4245804789/10000000000 : ℝ)*X 1 1+(4499724367/10000000000 : ℝ)*X 1 2+(2185455527/5000000000 : ℝ)*X 2 0+(4245804789/10000000000 : ℝ)*X 2 1+(4499724367/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1098_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1094056787/5000000000 : ℝ)*X 0 0+(5265362221/10000000000 : ℝ)*X 0 1+(337091039/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1098_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1328096007/2500000000 : ℝ)*X 1 0+(-2125001809/10000000000 : ℝ)*X 1 1+(269672831/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1098_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312383889/10000000000 : ℝ)*X 2 0+(2696728379/5000000000 : ℝ)*X 2 1+(-2125001809/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1098_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((546365069/1250000000 : ℝ)*X 0 0+(562385939/1250000000 : ℝ)*X 0 1+(1061611069/2500000000 : ℝ)*X 0 2+(546365069/1250000000 : ℝ)*X 1 0+(562385939/1250000000 : ℝ)*X 1 1+(1061611069/2500000000 : ℝ)*X 1 2+(546365069/1250000000 : ℝ)*X 2 0+(562385939/1250000000 : ℝ)*X 2 1+(1061611069/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1098_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (615131653669535576000639899/56875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1127247157/50000000000000 : ℝ)*(base19) + (1541518317/100000000000000 : ℝ)*(base23) + (1895213/2500000000000 : ℝ)*(lower2) + (156814901/50000000000000 : ℝ)*(upper3) + (4209209/1250000000000 : ℝ)*(upper5) + (2926504854476503/50000000000000 : ℝ)*(major0) + (2926504854476503/50000000000000 : ℝ)*(major1) + (2926504854476503/50000000000000 : ℝ)*(major2) + (7767576412736609/100000000000000 : ℝ)*(sp0) + (3883835515011939/50000000000000 : ℝ)*(sp1) + (62141373943999/800000000000 : ℝ)*(sp2) + (1969150760506487/50000000000000 : ℝ)*(sp3) + (96871781583/100000000000000 : ℝ)*(sp4) + (22125929057/50000000000000 : ℝ)*(sp7) + (246146610804443/6250000000000 : ℝ)*(f.failure) + (485479580282387/6250000000000 : ℝ)*(f.sum) + (20094088972423/3412500000000000000000000000 : ℝ)*base65 + (3817617054086278367/227500000000000000000000000000000 : ℝ)*base67 + (4016512184156278367/227500000000000000000000000000000 : ℝ)*base69 + (1974512548036221633/227500000000000000000000000000000 : ℝ)*base72 + (25566681284621/6825000000000000000000000000 : ℝ)*base73 + (6944245568413778367/227500000000000000000000000000000 : ℝ)*base75 + (1218389183983778367/227500000000000000000000000000000 : ℝ)*base77 + (2223768512346278367/227500000000000000000000000000000 : ℝ)*base79 + (6009661599829/6825000000000000000000000000 : ℝ)*base82 + (2465251/625000000000000000000 : ℝ)*base90 + (2465251/625000000000000000000 : ℝ)*base92 + (2465251/625000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (8833288979250033689204459/4062500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (650425673/100000000000000 : ℝ)*(base19) + (117485651/25000000000000 : ℝ)*(base23) + (120915859/50000000000000 : ℝ)*(lower1) + (1715757/20000000000000 : ℝ)*(upper2) + (27333501/50000000000000 : ℝ)*(upper3) + (735303802875761/12500000000000 : ℝ)*(major0) + (735303802875761/12500000000000 : ℝ)*(major1) + (735303802875761/12500000000000 : ℝ)*(major2) + (124738827/10000000000000 : ℝ)*(sp2) + (554203857/100000000000000 : ℝ)*(sp3) + (975839816039993/12500000000000 : ℝ)*(sp4) + (780671787789427/10000000000000 : ℝ)*(sp5) + (780671681098907/10000000000000 : ℝ)*(sp6) + (247383855688131/6250000000000 : ℝ)*(sp7) + (15461493145367/390625000000 : ℝ)*(f.failure) + (975839816039993/12500000000000 : ℝ)*(f.sum) + (3211261538297/487500000000000000000000000 : ℝ)*base65 + (41178167567531847/8125000000000000000000000000000 : ℝ)*base67 + (39213744701281847/8125000000000000000000000000000 : ℝ)*base69 + (21746056465593153/8125000000000000000000000000000 : ℝ)*base72 + (164917667381/975000000000000000000000000 : ℝ)*base74 + (50316895656281847/8125000000000000000000000000000 : ℝ)*base75 + (33065422396843153/8125000000000000000000000000000 : ℝ)*base78 + (106045651043781847/8125000000000000000000000000000 : ℝ)*base79 + (8287552821131/975000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (338919/39062500000000000000 : ℝ)*base90 + (338919/39062500000000000000 : ℝ)*base92 + (338919/39062500000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1098_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4145/1024 : ℝ) ≤ p) (hpb : p ≤ (8291/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148615943/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1753/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5647/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2259/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7011/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1098_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1098_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4145/1024 : ℝ) ≤ p) (hpb : p ≤ (8291/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148615943/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14071/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11249/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2259/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7011/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1098_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1098_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1098_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4145/1024 : ℝ) ≤ p) (hpb : p ≤ (8291/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148615943/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14071/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11249/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2259/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7011/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1098_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
