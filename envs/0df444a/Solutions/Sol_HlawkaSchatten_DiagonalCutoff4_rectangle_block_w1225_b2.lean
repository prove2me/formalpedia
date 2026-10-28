-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1225_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:12:30.317842+00:00
-- url     : https://prove2.me/submissions/c4976b49-d830-49dc-95c3-ae9438529961

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
theorem support_rectangle_w1225_s6_0 (p : ℝ) (hpa : (8417/2048 : ℝ) ≤ p) (hpb : p ≤ (4209/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2127797087/10000000000 : ℝ)*x 0 + (2695864199/5000000000 : ℝ)*x 1 + (2633390019/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2127797087/10000000000 : ℝ)^4209 ≤ (2587527775841/20000000000000 : ℝ)^3185 := by
    have hnat : (2127797087 : ℕ)^4209*20000000000000^3185 ≤ 2587527775841^3185*10000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2127797087 10000000000 2587527775841 20000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2695864199/5000000000 : ℝ)^4209 ≤ (1105138413353/2500000000000 : ℝ)^3185 := by
    have hnat : (2695864199 : ℕ)^4209*2500000000000^3185 ≤ 1105138413353^3185*5000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695864199 5000000000 1105138413353 2500000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2633390019/5000000000 : ℝ)^4209 ≤ (8571364915223/20000000000000 : ℝ)^3185 := by
    have hnat : (2633390019 : ℕ)^4209*20000000000000^3185 ≤ 8571364915223^3185*5000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633390019 5000000000 8571364915223 20000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4209/1024 : ℝ)) 4209 3185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2127797087/10000000000 : ℝ), (2695864199/5000000000 : ℝ), (2633390019/5000000000 : ℝ)] ![(2587527775841/20000000000000 : ℝ), (1105138413353/2500000000000 : ℝ), (8571364915223/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2127797087/10000000000 : ℝ)|^4209 ≤ (2587527775841/20000000000000 : ℝ)^3185
        have hw : |(-2127797087/10000000000 : ℝ)|=(2127797087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2695864199/5000000000 : ℝ)|^4209 ≤ (1105138413353/2500000000000 : ℝ)^3185
        have hw : |(2695864199/5000000000 : ℝ)|=(2695864199/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2633390019/5000000000 : ℝ)|^4209 ≤ (8571364915223/20000000000000 : ℝ)^3185
        have hw : |(2633390019/5000000000 : ℝ)|=(2633390019/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1225_s6_1 (p : ℝ) (hpa : (8417/2048 : ℝ) ≤ p) (hpb : p ≤ (4209/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5344450611/10000000000 : ℝ)*x 0 + (-2191156411/10000000000 : ℝ)*x 1 + (5266779653/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344450611/10000000000 : ℝ)^4209 ≤ (2730876118471/6250000000000 : ℝ)^3185 := by
    have hnat : (5344450611 : ℕ)^4209*6250000000000^3185 ≤ 2730876118471^3185*10000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344450611 10000000000 2730876118471 6250000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2191156411/10000000000 : ℝ)^4209 ≤ (168114520701/1250000000000 : ℝ)^3185 := by
    have hnat : (2191156411 : ℕ)^4209*1250000000000^3185 ≤ 168114520701^3185*10000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2191156411 10000000000 168114520701 1250000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266779653/10000000000 : ℝ)^4209 ≤ (42856820436071/100000000000000 : ℝ)^3185 := by
    have hnat : (5266779653 : ℕ)^4209*100000000000000^3185 ≤ 42856820436071^3185*10000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266779653 10000000000 42856820436071 100000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4209/1024 : ℝ)) 4209 3185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344450611/10000000000 : ℝ), (-2191156411/10000000000 : ℝ), (5266779653/10000000000 : ℝ)] ![(2730876118471/6250000000000 : ℝ), (168114520701/1250000000000 : ℝ), (42856820436071/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344450611/10000000000 : ℝ)|^4209 ≤ (2730876118471/6250000000000 : ℝ)^3185
        have hw : |(5344450611/10000000000 : ℝ)|=(5344450611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2191156411/10000000000 : ℝ)|^4209 ≤ (168114520701/1250000000000 : ℝ)^3185
        have hw : |(-2191156411/10000000000 : ℝ)|=(2191156411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266779653/10000000000 : ℝ)|^4209 ≤ (42856820436071/100000000000000 : ℝ)^3185
        have hw : |(5266779653/10000000000 : ℝ)|=(5266779653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1225_s6_2 (p : ℝ) (hpa : (8417/2048 : ℝ) ≤ p) (hpb : p ≤ (4209/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5344450449/10000000000 : ℝ)*x 0 + (5266779799/10000000000 : ℝ)*x 1 + (-2191156433/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344450449/10000000000 : ℝ)^4209 ≤ (5461752018159/12500000000000 : ℝ)^3185 := by
    have hnat : (5344450449 : ℕ)^4209*12500000000000^3185 ≤ 5461752018159^3185*10000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344450449 10000000000 5461752018159 12500000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266779799/10000000000 : ℝ)^4209 ≤ (42856822006061/100000000000000 : ℝ)^3185 := by
    have hnat : (5266779799 : ℕ)^4209*100000000000000^3185 ≤ 42856822006061^3185*10000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266779799 10000000000 42856822006061 100000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2191156433/10000000000 : ℝ)^4209 ≤ (13449161834529/100000000000000 : ℝ)^3185 := by
    have hnat : (2191156433 : ℕ)^4209*100000000000000^3185 ≤ 13449161834529^3185*10000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2191156433 10000000000 13449161834529 100000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4209/1024 : ℝ)) 4209 3185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344450449/10000000000 : ℝ), (5266779799/10000000000 : ℝ), (-2191156433/10000000000 : ℝ)] ![(5461752018159/12500000000000 : ℝ), (42856822006061/100000000000000 : ℝ), (13449161834529/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344450449/10000000000 : ℝ)|^4209 ≤ (5461752018159/12500000000000 : ℝ)^3185
        have hw : |(5344450449/10000000000 : ℝ)|=(5344450449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266779799/10000000000 : ℝ)|^4209 ≤ (42856822006061/100000000000000 : ℝ)^3185
        have hw : |(5266779799/10000000000 : ℝ)|=(5266779799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2191156433/10000000000 : ℝ)|^4209 ≤ (13449161834529/100000000000000 : ℝ)^3185
        have hw : |(-2191156433/10000000000 : ℝ)|=(2191156433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1225_s6_3 (p : ℝ) (hpa : (8417/2048 : ℝ) ≤ p) (hpb : p ≤ (4209/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2176549519/5000000000 : ℝ)*x 0 + (845714133/2000000000 : ℝ)*x 1 + (4481206113/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2176549519/5000000000 : ℝ)^4209 ≤ (260291364357/781250000000 : ℝ)^3185 := by
    have hnat : (2176549519 : ℕ)^4209*781250000000^3185 ≤ 260291364357^3185*5000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2176549519 5000000000 260291364357 781250000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (845714133/2000000000 : ℝ)^4209 ≤ (32063593353433/100000000000000 : ℝ)^3185 := by
    have hnat : (845714133 : ℕ)^4209*100000000000000^3185 ≤ 32063593353433^3185*2000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      845714133 2000000000 32063593353433 100000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4481206113/10000000000 : ℝ)^4209 ≤ (8654777999647/25000000000000 : ℝ)^3185 := by
    have hnat : (4481206113 : ℕ)^4209*25000000000000^3185 ≤ 8654777999647^3185*10000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4481206113 10000000000 8654777999647 25000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4209/1024 : ℝ)) 4209 3185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2176549519/5000000000 : ℝ), (845714133/2000000000 : ℝ), (4481206113/10000000000 : ℝ)] ![(260291364357/781250000000 : ℝ), (32063593353433/100000000000000 : ℝ), (8654777999647/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2176549519/5000000000 : ℝ)|^4209 ≤ (260291364357/781250000000 : ℝ)^3185
        have hw : |(2176549519/5000000000 : ℝ)|=(2176549519/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(845714133/2000000000 : ℝ)|^4209 ≤ (32063593353433/100000000000000 : ℝ)^3185
        have hw : |(845714133/2000000000 : ℝ)|=(845714133/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4481206113/10000000000 : ℝ)|^4209 ≤ (8654777999647/25000000000000 : ℝ)^3185
        have hw : |(4481206113/10000000000 : ℝ)|=(4481206113/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1225_s6_4 (p : ℝ) (hpa : (8417/2048 : ℝ) ≤ p) (hpb : p ≤ (4209/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-132987667/625000000 : ℝ)*x 0 + (2633547667/5000000000 : ℝ)*x 1 + (5391411321/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (132987667/625000000 : ℝ)^4209 ≤ (12937683755569/100000000000000 : ℝ)^3185 := by
    have hnat : (132987667 : ℕ)^4209*100000000000000^3185 ≤ 12937683755569^3185*625000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132987667 625000000 12937683755569 100000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633547667/5000000000 : ℝ)^4209 ≤ (21430107550507/50000000000000 : ℝ)^3185 := by
    have hnat : (2633547667 : ℕ)^4209*50000000000000^3185 ≤ 21430107550507^3185*5000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633547667 5000000000 21430107550507 50000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5391411321/10000000000 : ℝ)^4209 ≤ (44202101122479/100000000000000 : ℝ)^3185 := by
    have hnat : (5391411321 : ℕ)^4209*100000000000000^3185 ≤ 44202101122479^3185*10000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391411321 10000000000 44202101122479 100000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4209/1024 : ℝ)) 4209 3185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-132987667/625000000 : ℝ), (2633547667/5000000000 : ℝ), (5391411321/10000000000 : ℝ)] ![(12937683755569/100000000000000 : ℝ), (21430107550507/50000000000000 : ℝ), (44202101122479/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-132987667/625000000 : ℝ)|^4209 ≤ (12937683755569/100000000000000 : ℝ)^3185
        have hw : |(-132987667/625000000 : ℝ)|=(132987667/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633547667/5000000000 : ℝ)|^4209 ≤ (21430107550507/50000000000000 : ℝ)^3185
        have hw : |(2633547667/5000000000 : ℝ)|=(2633547667/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5391411321/10000000000 : ℝ)|^4209 ≤ (44202101122479/100000000000000 : ℝ)^3185
        have hw : |(5391411321/10000000000 : ℝ)|=(5391411321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1225_s6_5 (p : ℝ) (hpa : (8417/2048 : ℝ) ≤ p) (hpb : p ≤ (4209/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5312606399/10000000000 : ℝ)*x 0 + (-2066524153/10000000000 : ℝ)*x 1 + (134785291/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312606399/10000000000 : ℝ)^4209 ≤ (43350299980997/100000000000000 : ℝ)^3185 := by
    have hnat : (5312606399 : ℕ)^4209*100000000000000^3185 ≤ 43350299980997^3185*10000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312606399 10000000000 43350299980997 100000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2066524153/10000000000 : ℝ)^4209 ≤ (12447595424043/100000000000000 : ℝ)^3185 := by
    have hnat : (2066524153 : ℕ)^4209*100000000000000^3185 ≤ 12447595424043^3185*10000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2066524153 10000000000 12447595424043 100000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (134785291/250000000 : ℝ)^4209 ≤ (44202104578693/100000000000000 : ℝ)^3185 := by
    have hnat : (134785291 : ℕ)^4209*100000000000000^3185 ≤ 44202104578693^3185*250000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      134785291 250000000 44202104578693 100000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4209/1024 : ℝ)) 4209 3185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312606399/10000000000 : ℝ), (-2066524153/10000000000 : ℝ), (134785291/250000000 : ℝ)] ![(43350299980997/100000000000000 : ℝ), (12447595424043/100000000000000 : ℝ), (44202104578693/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312606399/10000000000 : ℝ)|^4209 ≤ (43350299980997/100000000000000 : ℝ)^3185
        have hw : |(5312606399/10000000000 : ℝ)|=(5312606399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2066524153/10000000000 : ℝ)|^4209 ≤ (12447595424043/100000000000000 : ℝ)^3185
        have hw : |(-2066524153/10000000000 : ℝ)|=(2066524153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(134785291/250000000 : ℝ)|^4209 ≤ (44202104578693/100000000000000 : ℝ)^3185
        have hw : |(134785291/250000000 : ℝ)|=(134785291/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1225_s6_6 (p : ℝ) (hpa : (8417/2048 : ℝ) ≤ p) (hpb : p ≤ (4209/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5312606023/10000000000 : ℝ)*x 0 + (5391411247/10000000000 : ℝ)*x 1 + (-516631299/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312606023/10000000000 : ℝ)^4209 ≤ (8670059185291/20000000000000 : ℝ)^3185 := by
    have hnat : (5312606023 : ℕ)^4209*20000000000000^3185 ≤ 8670059185291^3185*10000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312606023 10000000000 8670059185291 20000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5391411247/10000000000 : ℝ)^4209 ≤ (11050525080181/25000000000000 : ℝ)^3185 := by
    have hnat : (5391411247 : ℕ)^4209*25000000000000^3185 ≤ 11050525080181^3185*10000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391411247 10000000000 11050525080181 25000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (516631299/2500000000 : ℝ)^4209 ≤ (12447603726351/100000000000000 : ℝ)^3185 := by
    have hnat : (516631299 : ℕ)^4209*100000000000000^3185 ≤ 12447603726351^3185*2500000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      516631299 2500000000 12447603726351 100000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4209/1024 : ℝ)) 4209 3185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312606023/10000000000 : ℝ), (5391411247/10000000000 : ℝ), (-516631299/2500000000 : ℝ)] ![(8670059185291/20000000000000 : ℝ), (11050525080181/25000000000000 : ℝ), (12447603726351/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312606023/10000000000 : ℝ)|^4209 ≤ (8670059185291/20000000000000 : ℝ)^3185
        have hw : |(5312606023/10000000000 : ℝ)|=(5312606023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5391411247/10000000000 : ℝ)|^4209 ≤ (11050525080181/25000000000000 : ℝ)^3185
        have hw : |(5391411247/10000000000 : ℝ)|=(5391411247/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-516631299/2500000000 : ℝ)|^4209 ≤ (12447603726351/100000000000000 : ℝ)^3185
        have hw : |(-516631299/2500000000 : ℝ)|=(516631299/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1225_s6_7 (p : ℝ) (hpa : (8417/2048 : ℝ) ≤ p) (hpb : p ≤ (4209/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (870621769/2000000000 : ℝ)*x 0 + (560070881/1250000000 : ℝ)*x 1 + (2114605917/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (870621769/2000000000 : ℝ)^4209 ≤ (33317393829777/100000000000000 : ℝ)^3185 := by
    have hnat : (870621769 : ℕ)^4209*100000000000000^3185 ≤ 33317393829777^3185*2000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      870621769 2000000000 33317393829777 100000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (560070881/1250000000 : ℝ)^4209 ≤ (17306293912037/50000000000000 : ℝ)^3185 := by
    have hnat : (560070881 : ℕ)^4209*50000000000000^3185 ≤ 17306293912037^3185*1250000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      560070881 1250000000 17306293912037 50000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2114605917/5000000000 : ℝ)^4209 ≤ (6414003664941/20000000000000 : ℝ)^3185 := by
    have hnat : (2114605917 : ℕ)^4209*20000000000000^3185 ≤ 6414003664941^3185*5000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2114605917 5000000000 6414003664941 20000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4209/1024 : ℝ)) 4209 3185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(870621769/2000000000 : ℝ), (560070881/1250000000 : ℝ), (2114605917/5000000000 : ℝ)] ![(33317393829777/100000000000000 : ℝ), (17306293912037/50000000000000 : ℝ), (6414003664941/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(870621769/2000000000 : ℝ)|^4209 ≤ (33317393829777/100000000000000 : ℝ)^3185
        have hw : |(870621769/2000000000 : ℝ)|=(870621769/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(560070881/1250000000 : ℝ)|^4209 ≤ (17306293912037/50000000000000 : ℝ)^3185
        have hw : |(560070881/1250000000 : ℝ)|=(560070881/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2114605917/5000000000 : ℝ)|^4209 ≤ (6414003664941/20000000000000 : ℝ)^3185
        have hw : |(2114605917/5000000000 : ℝ)|=(2114605917/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1225_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8417/2048 : ℝ) ≤ p) (hpb : p ≤ (4209/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37773923/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14123/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11431/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11453/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (141/1000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14123/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11431/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14123/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11431/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14123/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11431/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14123/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11431/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14123/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11431/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14123/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11431/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11431/100000 : ℝ) ^ (8417/2048 : ℝ) ≤ (13454108982228399/100000000000000000000 : ℝ) := by
    have hpowers : (11431/100000 : ℝ)^8417 ≤ (13454108982228399/100000000000000000000 : ℝ)^2048 := by
      have hnat : (11431 : ℕ)^8417*100000000000000000000^2048 ≤ 13454108982228399^2048*100000^8417 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11431 100000 13454108982228399 100000000000000000000 8417 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11431/100000 : ℝ)) (X := (13454108982228399/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8417 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14123/100000 : ℝ) ^ (8417/2048 : ℝ) ≤ (32086032782078819/100000000000000000000 : ℝ) := by
    have hpowers : (14123/100000 : ℝ)^8417 ≤ (32086032782078819/100000000000000000000 : ℝ)^2048 := by
      have hnat : (14123 : ℕ)^8417*100000000000000000000^2048 ≤ 32086032782078819^2048*100000^8417 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14123 100000 32086032782078819 100000000000000000000 8417 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14123/100000 : ℝ)) (X := (32086032782078819/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8417 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013454108982228399/50000000000000000000 : ℝ) ≤ (5000327328151391/5000000000000000 : ℝ) ^ (8417/2048 : ℝ) := by
    have hpowers : (50013454108982228399/50000000000000000000 : ℝ)^2048 ≤ (5000327328151391/5000000000000000 : ℝ)^8417 := by
      have hnat : (50013454108982228399 : ℕ)^2048*5000000000000000^8417 ≤ 5000327328151391^8417*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013454108982228399 50000000000000000000 5000327328151391 5000000000000000 2048 8417 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000327328151391/5000000000000000 : ℝ)) (X := (50013454108982228399/50000000000000000000 : ℝ)) (by norm_num) 8417 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50022770070882153609/50000000000000000000 : ℝ) ≤ (10001107878639743/10000000000000000 : ℝ) ^ (8417/2048 : ℝ) := by
    have hpowers : (50022770070882153609/50000000000000000000 : ℝ)^2048 ≤ (10001107878639743/10000000000000000 : ℝ)^8417 := by
      have hnat : (50022770070882153609 : ℕ)^2048*10000000000000000^8417 ≤ 10001107878639743^8417*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50022770070882153609 50000000000000000000 10001107878639743 10000000000000000 2048 8417 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001107878639743/10000000000000000 : ℝ)) (X := (50022770070882153609/50000000000000000000 : ℝ)) (by norm_num) 8417 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50032086032782078819/50000000000000000000 : ℝ) ≤ (156274392202761/156250000000000 : ℝ) ^ (8417/2048 : ℝ) := by
    have hpowers : (50032086032782078819/50000000000000000000 : ℝ)^2048 ≤ (156274392202761/156250000000000 : ℝ)^8417 := by
      have hnat : (50032086032782078819 : ℕ)^2048*156250000000000^8417 ≤ 156274392202761^8417*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50032086032782078819 50000000000000000000 156274392202761 156250000000000 2048 8417 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (156274392202761/156250000000000 : ℝ)) (X := (50032086032782078819/50000000000000000000 : ℝ)) (by norm_num) 8417 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13454108982228399/100000000000000000000 : ℝ) ≤ ((13455700382849743381/13460000000000000000 : ℝ)+2*(453222336961/269200000000000 : ℝ)*(11431/100000 : ℝ))^(8417/2048 : ℝ) := by
    rw [show (13455700382849743381/13460000000000000000 : ℝ)+2*(453222336961/269200000000000 : ℝ)*(11431/100000 : ℝ)=(5000327328151391/5000000000000000 : ℝ) by norm_num, show 1+2*(13454108982228399/100000000000000000000 : ℝ)=(50013454108982228399/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(32086032782078819/100000000000000000000 : ℝ)+(13454108982228399/100000000000000000000 : ℝ) ≤ ((13455700382849743381/13460000000000000000 : ℝ)+(453222336961/269200000000000 : ℝ)*((14123/100000 : ℝ)+(11431/100000 : ℝ)))^(8417/2048 : ℝ) := by
    rw [show (13455700382849743381/13460000000000000000 : ℝ)+(453222336961/269200000000000 : ℝ)*((14123/100000 : ℝ)+(11431/100000 : ℝ))=(10001107878639743/10000000000000000 : ℝ) by norm_num, show 1+(32086032782078819/100000000000000000000 : ℝ)+(13454108982228399/100000000000000000000 : ℝ)=(50022770070882153609/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(32086032782078819/100000000000000000000 : ℝ) ≤ ((13455700382849743381/13460000000000000000 : ℝ)+2*(453222336961/269200000000000 : ℝ)*(14123/100000 : ℝ))^(8417/2048 : ℝ) := by
    rw [show (13455700382849743381/13460000000000000000 : ℝ)+2*(453222336961/269200000000000 : ℝ)*(14123/100000 : ℝ)=(156274392202761/156250000000000 : ℝ) by norm_num, show 1+2*(32086032782078819/100000000000000000000 : ℝ)=(50032086032782078819/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13455700382849743381/13460000000000000000 : ℝ)*(X 1 0+X 2 0)+(453222336961/269200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8417/2048 : ℝ)) (lo := (11431/100000 : ℝ)) (hi := (14123/100000 : ℝ)) (c := (13455700382849743381/13460000000000000000 : ℝ)) (alpha := (453222336961/269200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13455700382849743381/13460000000000000000 : ℝ)*(X 0 1+X 2 1)+(453222336961/269200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8417/2048 : ℝ)) (lo := (11431/100000 : ℝ)) (hi := (14123/100000 : ℝ)) (c := (13455700382849743381/13460000000000000000 : ℝ)) (alpha := (453222336961/269200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13455700382849743381/13460000000000000000 : ℝ)*(X 0 2+X 1 2)+(453222336961/269200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8417/2048 : ℝ)) (lo := (11431/100000 : ℝ)) (hi := (14123/100000 : ℝ)) (c := (13455700382849743381/13460000000000000000 : ℝ)) (alpha := (453222336961/269200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2127797087/10000000000 : ℝ)*X 0 0+(2695864199/5000000000 : ℝ)*X 0 1+(2633390019/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1225_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344450611/10000000000 : ℝ)*X 1 0+(-2191156411/10000000000 : ℝ)*X 1 1+(5266779653/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1225_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344450449/10000000000 : ℝ)*X 2 0+(5266779799/10000000000 : ℝ)*X 2 1+(-2191156433/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1225_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2176549519/5000000000 : ℝ)*X 0 0+(845714133/2000000000 : ℝ)*X 0 1+(4481206113/10000000000 : ℝ)*X 0 2+(2176549519/5000000000 : ℝ)*X 1 0+(845714133/2000000000 : ℝ)*X 1 1+(4481206113/10000000000 : ℝ)*X 1 2+(2176549519/5000000000 : ℝ)*X 2 0+(845714133/2000000000 : ℝ)*X 2 1+(4481206113/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1225_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-132987667/625000000 : ℝ)*X 0 0+(2633547667/5000000000 : ℝ)*X 0 1+(5391411321/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1225_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312606399/10000000000 : ℝ)*X 1 0+(-2066524153/10000000000 : ℝ)*X 1 1+(134785291/250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1225_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312606023/10000000000 : ℝ)*X 2 0+(5391411247/10000000000 : ℝ)*X 2 1+(-516631299/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1225_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((870621769/2000000000 : ℝ)*X 0 0+(560070881/1250000000 : ℝ)*X 0 1+(2114605917/5000000000 : ℝ)*X 0 2+(870621769/2000000000 : ℝ)*X 1 0+(560070881/1250000000 : ℝ)*X 1 1+(2114605917/5000000000 : ℝ)*X 1 2+(870621769/2000000000 : ℝ)*X 2 0+(560070881/1250000000 : ℝ)*X 2 1+(2114605917/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1225_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1782330315400456296642603057/168250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (797318871/50000000000000 : ℝ)*(base19) + (77349997/6250000000000 : ℝ)*(base23) + (9263281/12500000000000 : ℝ)*(lower2) + (164180463/100000000000000 : ℝ)*(upper3) + (6471793/50000000000000 : ℝ)*(lower4) + (2990417601992601/50000000000000 : ℝ)*(major0) + (2990417601992601/50000000000000 : ℝ)*(major1) + (2990417601992601/50000000000000 : ℝ)*(major2) + (8003337842001237/100000000000000 : ℝ)*(sp0) + (8003358911603971/100000000000000 : ℝ)*(sp1) + (8003359268641761/100000000000000 : ℝ)*(sp2) + (1979144863864389/50000000000000 : ℝ)*(sp3) + (906569619/4000000000000 : ℝ)*(sp4) + (49552221/250000000000 : ℝ)*(sp7) + (1979154774308589/50000000000000 : ℝ)*(f.failure) + (500210031640107/6250000000000 : ℝ)*(f.sum) + (19243205098289/6730000000000000000000000000 : ℝ)*base66 + (5077463084930773981/673000000000000000000000000000000 : ℝ)*base67 + (3773890721753773981/673000000000000000000000000000000 : ℝ)*base69 + (9937413262703773981/673000000000000000000000000000000 : ℝ)*base71 + (6581388174591/6730000000000000000000000000 : ℝ)*base73 + (8523486690932226019/673000000000000000000000000000000 : ℝ)*base76 + (922158036119773981/673000000000000000000000000000000 : ℝ)*base77 + (5217370320531773981/673000000000000000000000000000000 : ℝ)*base79 + (33753665508831/6730000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (5875353/1250000000000000000000 : ℝ)*base90 + (5875353/1250000000000000000000 : ℝ)*base92 + (5875353/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (604000402715183864293653213/673000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1558112389/100000000000000 : ℝ)*(base19) + (1706661213/100000000000000 : ℝ)*(base23) + (572615151/100000000000000 : ℝ)*(upper2) + (35407761/50000000000000 : ℝ)*(upper3) + (490185851/100000000000000 : ℝ)*(upper5) + (6011212800571491/100000000000000 : ℝ)*(major0) + (6011212800571491/100000000000000 : ℝ)*(major1) + (6011212800571491/100000000000000 : ℝ)*(major2) + (18130544151/25000000000000 : ℝ)*(sp1) + (12466515759/100000000000000 : ℝ)*(sp2) + (8044011149873903/100000000000000 : ℝ)*(sp4) + (8043937069584909/100000000000000 : ℝ)*(sp5) + (8043996976696931/100000000000000 : ℝ)*(sp6) + (994603605338313/25000000000000 : ℝ)*(sp7) + (994603605338313/25000000000000 : ℝ)*(f.failure) + (8044011149873903/100000000000000 : ℝ)*(f.sum) + (30154567190189/13460000000000000000000000000 : ℝ)*base66 + (2144346960929101071/1346000000000000000000000000000000 : ℝ)*base67 + (22704874213288898929/1346000000000000000000000000000000 : ℝ)*base70 + (8751580886112898929/1346000000000000000000000000000000 : ℝ)*base72 + (78427526707351/13460000000000000000000000000 : ℝ)*base73 + (5272915812797101071/1346000000000000000000000000000000 : ℝ)*base75 + (13872307955386898929/1346000000000000000000000000000000 : ℝ)*base78 + (4505521346486898929/1346000000000000000000000000000000 : ℝ)*base80 + (29440418393151/13460000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (5461899/625000000000000000000 : ℝ)*base89 + (5461899/625000000000000000000 : ℝ)*base91 + (5461899/625000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1225_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8417/2048 : ℝ) ≤ p) (hpb : p ≤ (4209/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37773923/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14123/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11431/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11453/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (141/1000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1225_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1225_s7_0 (p : ℝ) (hpa : (8417/2048 : ℝ) ≤ p) (hpb : p ≤ (4209/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2127815533/10000000000 : ℝ)*x 0 + (5391513957/10000000000 : ℝ)*x 1 + (1053396463/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2127815533/10000000000 : ℝ)^4209 ≤ (1617223386987/12500000000000 : ℝ)^3185 := by
    have hnat : (2127815533 : ℕ)^4209*12500000000000^3185 ≤ 1617223386987^3185*10000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2127815533 10000000000 1617223386987 12500000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5391513957/10000000000 : ℝ)^4209 ≤ (8840642627669/20000000000000 : ℝ)^3185 := by
    have hnat : (5391513957 : ℕ)^4209*20000000000000^3185 ≤ 8840642627669^3185*10000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391513957 10000000000 8840642627669 20000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1053396463/2000000000 : ℝ)^4209 ≤ (42858999747507/100000000000000 : ℝ)^3185 := by
    have hnat : (1053396463 : ℕ)^4209*100000000000000^3185 ≤ 42858999747507^3185*2000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053396463 2000000000 42858999747507 100000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4209/1024 : ℝ)) 4209 3185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2127815533/10000000000 : ℝ), (5391513957/10000000000 : ℝ), (1053396463/2000000000 : ℝ)] ![(1617223386987/12500000000000 : ℝ), (8840642627669/20000000000000 : ℝ), (42858999747507/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2127815533/10000000000 : ℝ)|^4209 ≤ (1617223386987/12500000000000 : ℝ)^3185
        have hw : |(-2127815533/10000000000 : ℝ)|=(2127815533/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5391513957/10000000000 : ℝ)|^4209 ≤ (8840642627669/20000000000000 : ℝ)^3185
        have hw : |(5391513957/10000000000 : ℝ)|=(5391513957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1053396463/2000000000 : ℝ)|^4209 ≤ (42858999747507/100000000000000 : ℝ)^3185
        have hw : |(1053396463/2000000000 : ℝ)|=(1053396463/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1225_s7_1 (p : ℝ) (hpa : (8417/2048 : ℝ) ≤ p) (hpb : p ≤ (4209/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2672198101/5000000000 : ℝ)*x 0 + (-219096023/1000000000 : ℝ)*x 1 + (1053396459/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672198101/5000000000 : ℝ)^4209 ≤ (43693430056481/100000000000000 : ℝ)^3185 := by
    have hnat : (2672198101 : ℕ)^4209*100000000000000^3185 ≤ 43693430056481^3185*5000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672198101 5000000000 43693430056481 100000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (219096023/1000000000 : ℝ)^4209 ≤ (3361892598223/25000000000000 : ℝ)^3185 := by
    have hnat : (219096023 : ℕ)^4209*25000000000000^3185 ≤ 3361892598223^3185*1000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      219096023 1000000000 3361892598223 25000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1053396459/2000000000 : ℝ)^4209 ≤ (21429499766219/50000000000000 : ℝ)^3185 := by
    have hnat : (1053396459 : ℕ)^4209*50000000000000^3185 ≤ 21429499766219^3185*2000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053396459 2000000000 21429499766219 50000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4209/1024 : ℝ)) 4209 3185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672198101/5000000000 : ℝ), (-219096023/1000000000 : ℝ), (1053396459/2000000000 : ℝ)] ![(43693430056481/100000000000000 : ℝ), (3361892598223/25000000000000 : ℝ), (21429499766219/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672198101/5000000000 : ℝ)|^4209 ≤ (43693430056481/100000000000000 : ℝ)^3185
        have hw : |(2672198101/5000000000 : ℝ)|=(2672198101/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-219096023/1000000000 : ℝ)|^4209 ≤ (3361892598223/25000000000000 : ℝ)^3185
        have hw : |(-219096023/1000000000 : ℝ)|=(219096023/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1053396459/2000000000 : ℝ)|^4209 ≤ (21429499766219/50000000000000 : ℝ)^3185
        have hw : |(1053396459/2000000000 : ℝ)|=(1053396459/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1225_s7_2 (p : ℝ) (hpa : (8417/2048 : ℝ) ≤ p) (hpb : p ≤ (4209/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (668049523/1250000000 : ℝ)*x 0 + (5266982311/10000000000 : ℝ)*x 1 + (-2190960233/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668049523/1250000000 : ℝ)^4209 ≤ (5461678732751/12500000000000 : ℝ)^3185 := by
    have hnat : (668049523 : ℕ)^4209*12500000000000^3185 ≤ 5461678732751^3185*1250000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668049523 1250000000 5461678732751 12500000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266982311/10000000000 : ℝ)^4209 ≤ (42858999704493/100000000000000 : ℝ)^3185 := by
    have hnat : (5266982311 : ℕ)^4209*100000000000000^3185 ≤ 42858999704493^3185*10000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266982311 10000000000 42858999704493 100000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2190960233/10000000000 : ℝ)^4209 ≤ (537902816689/4000000000000 : ℝ)^3185 := by
    have hnat : (2190960233 : ℕ)^4209*4000000000000^3185 ≤ 537902816689^3185*10000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2190960233 10000000000 537902816689 4000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4209/1024 : ℝ)) 4209 3185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668049523/1250000000 : ℝ), (5266982311/10000000000 : ℝ), (-2190960233/10000000000 : ℝ)] ![(5461678732751/12500000000000 : ℝ), (42858999704493/100000000000000 : ℝ), (537902816689/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668049523/1250000000 : ℝ)|^4209 ≤ (5461678732751/12500000000000 : ℝ)^3185
        have hw : |(668049523/1250000000 : ℝ)|=(668049523/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266982311/10000000000 : ℝ)|^4209 ≤ (42858999704493/100000000000000 : ℝ)^3185
        have hw : |(5266982311/10000000000 : ℝ)|=(5266982311/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2190960233/10000000000 : ℝ)|^4209 ≤ (537902816689/4000000000000 : ℝ)^3185
        have hw : |(-2190960233/10000000000 : ℝ)|=(2190960233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1225_s7_3 (p : ℝ) (hpa : (8417/2048 : ℝ) ≤ p) (hpb : p ≤ (4209/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4353109897/10000000000 : ℝ)*x 0 + (2114495379/5000000000 : ℝ)*x 1 + (4480783013/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4353109897/10000000000 : ℝ)^4209 ≤ (8329351117537/25000000000000 : ℝ)^3185 := by
    have hnat : (4353109897 : ℕ)^4209*25000000000000^3185 ≤ 8329351117537^3185*10000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4353109897 10000000000 8329351117537 25000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2114495379/5000000000 : ℝ)^4209 ≤ (16033901474963/50000000000000 : ℝ)^3185 := by
    have hnat : (2114495379 : ℕ)^4209*50000000000000^3185 ≤ 16033901474963^3185*5000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2114495379 5000000000 16033901474963 50000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4480783013/10000000000 : ℝ)^4209 ≤ (34614792563751/100000000000000 : ℝ)^3185 := by
    have hnat : (4480783013 : ℕ)^4209*100000000000000^3185 ≤ 34614792563751^3185*10000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4480783013 10000000000 34614792563751 100000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4209/1024 : ℝ)) 4209 3185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4353109897/10000000000 : ℝ), (2114495379/5000000000 : ℝ), (4480783013/10000000000 : ℝ)] ![(8329351117537/25000000000000 : ℝ), (16033901474963/50000000000000 : ℝ), (34614792563751/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4353109897/10000000000 : ℝ)|^4209 ≤ (8329351117537/25000000000000 : ℝ)^3185
        have hw : |(4353109897/10000000000 : ℝ)|=(4353109897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2114495379/5000000000 : ℝ)|^4209 ≤ (16033901474963/50000000000000 : ℝ)^3185
        have hw : |(2114495379/5000000000 : ℝ)|=(2114495379/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4480783013/10000000000 : ℝ)|^4209 ≤ (34614792563751/100000000000000 : ℝ)^3185
        have hw : |(4480783013/10000000000 : ℝ)|=(4480783013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1225_s7_4 (p : ℝ) (hpa : (8417/2048 : ℝ) ≤ p) (hpb : p ≤ (4209/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1063910117/5000000000 : ℝ)*x 0 + (5267296931/10000000000 : ℝ)*x 1 + (1347799551/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1063910117/5000000000 : ℝ)^4209 ≤ (6468912434641/50000000000000 : ℝ)^3185 := by
    have hnat : (1063910117 : ℕ)^4209*50000000000000^3185 ≤ 6468912434641^3185*5000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1063910117 5000000000 6468912434641 50000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5267296931/10000000000 : ℝ)^4209 ≤ (42862383001753/100000000000000 : ℝ)^3185 := by
    have hnat : (5267296931 : ℕ)^4209*100000000000000^3185 ≤ 42862383001753^3185*10000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267296931 10000000000 42862383001753 100000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1347799551/2500000000 : ℝ)^4209 ≤ (8839958423073/20000000000000 : ℝ)^3185 := by
    have hnat : (1347799551 : ℕ)^4209*20000000000000^3185 ≤ 8839958423073^3185*2500000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1347799551 2500000000 8839958423073 20000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4209/1024 : ℝ)) 4209 3185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1063910117/5000000000 : ℝ), (5267296931/10000000000 : ℝ), (1347799551/2500000000 : ℝ)] ![(6468912434641/50000000000000 : ℝ), (42862383001753/100000000000000 : ℝ), (8839958423073/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1063910117/5000000000 : ℝ)|^4209 ≤ (6468912434641/50000000000000 : ℝ)^3185
        have hw : |(-1063910117/5000000000 : ℝ)|=(1063910117/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5267296931/10000000000 : ℝ)|^4209 ≤ (42862383001753/100000000000000 : ℝ)^3185
        have hw : |(5267296931/10000000000 : ℝ)|=(5267296931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1347799551/2500000000 : ℝ)|^4209 ≤ (8839958423073/20000000000000 : ℝ)^3185
        have hw : |(1347799551/2500000000 : ℝ)|=(1347799551/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1225_s7_5 (p : ℝ) (hpa : (8417/2048 : ℝ) ≤ p) (hpb : p ≤ (4209/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (132816449/250000000 : ℝ)*x 0 + (-1033371581/5000000000 : ℝ)*x 1 + (1078239883/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (132816449/250000000 : ℝ)^4209 ≤ (21675427991249/50000000000000 : ℝ)^3185 := by
    have hnat : (132816449 : ℕ)^4209*50000000000000^3185 ≤ 21675427991249^3185*250000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132816449 250000000 21675427991249 50000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1033371581/5000000000 : ℝ)^4209 ≤ (12449338771003/100000000000000 : ℝ)^3185 := by
    have hnat : (1033371581 : ℕ)^4209*100000000000000^3185 ≤ 12449338771003^3185*5000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1033371581 5000000000 12449338771003 100000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1078239883/2000000000 : ℝ)^4209 ≤ (44199805235811/100000000000000 : ℝ)^3185 := by
    have hnat : (1078239883 : ℕ)^4209*100000000000000^3185 ≤ 44199805235811^3185*2000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078239883 2000000000 44199805235811 100000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4209/1024 : ℝ)) 4209 3185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(132816449/250000000 : ℝ), (-1033371581/5000000000 : ℝ), (1078239883/2000000000 : ℝ)] ![(21675427991249/50000000000000 : ℝ), (12449338771003/100000000000000 : ℝ), (44199805235811/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(132816449/250000000 : ℝ)|^4209 ≤ (21675427991249/50000000000000 : ℝ)^3185
        have hw : |(132816449/250000000 : ℝ)|=(132816449/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1033371581/5000000000 : ℝ)|^4209 ≤ (12449338771003/100000000000000 : ℝ)^3185
        have hw : |(-1033371581/5000000000 : ℝ)|=(1033371581/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1078239883/2000000000 : ℝ)|^4209 ≤ (44199805235811/100000000000000 : ℝ)^3185
        have hw : |(1078239883/2000000000 : ℝ)|=(1078239883/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1225_s7_6 (p : ℝ) (hpa : (8417/2048 : ℝ) ≤ p) (hpb : p ≤ (4209/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (332041161/625000000 : ℝ)*x 0 + (2695599149/5000000000 : ℝ)*x 1 + (-2066743847/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (332041161/625000000 : ℝ)^4209 ≤ (43350862625067/100000000000000 : ℝ)^3185 := by
    have hnat : (332041161 : ℕ)^4209*100000000000000^3185 ≤ 43350862625067^3185*625000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      332041161 625000000 43350862625067 100000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2695599149/5000000000 : ℝ)^4209 ≤ (22099896566899/50000000000000 : ℝ)^3185 := by
    have hnat : (2695599149 : ℕ)^4209*50000000000000^3185 ≤ 22099896566899^3185*5000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695599149 5000000000 22099896566899 50000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2066743847/10000000000 : ℝ)^4209 ≤ (6224672111903/50000000000000 : ℝ)^3185 := by
    have hnat : (2066743847 : ℕ)^4209*50000000000000^3185 ≤ 6224672111903^3185*10000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2066743847 10000000000 6224672111903 50000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4209/1024 : ℝ)) 4209 3185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(332041161/625000000 : ℝ), (2695599149/5000000000 : ℝ), (-2066743847/10000000000 : ℝ)] ![(43350862625067/100000000000000 : ℝ), (22099896566899/50000000000000 : ℝ), (6224672111903/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(332041161/625000000 : ℝ)|^4209 ≤ (43350862625067/100000000000000 : ℝ)^3185
        have hw : |(332041161/625000000 : ℝ)|=(332041161/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2695599149/5000000000 : ℝ)|^4209 ≤ (22099896566899/50000000000000 : ℝ)^3185
        have hw : |(2695599149/5000000000 : ℝ)|=(2695599149/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2066743847/10000000000 : ℝ)|^4209 ≤ (6224672111903/50000000000000 : ℝ)^3185
        have hw : |(-2066743847/10000000000 : ℝ)|=(2066743847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1225_s7_7 (p : ℝ) (hpa : (8417/2048 : ℝ) ≤ p) (hpb : p ≤ (4209/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4353119447/10000000000 : ℝ)*x 0 + (448014901/1000000000 : ℝ)*x 1 + (422962699/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4353119447/10000000000 : ℝ)^4209 ≤ (333175010629/1000000000000 : ℝ)^3185 := by
    have hnat : (4353119447 : ℕ)^4209*1000000000000^3185 ≤ 333175010629^3185*10000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4353119447 10000000000 333175010629 1000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (448014901/1000000000 : ℝ)^4209 ≤ (34608320262199/100000000000000 : ℝ)^3185 := by
    have hnat : (448014901 : ℕ)^4209*100000000000000^3185 ≤ 34608320262199^3185*1000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      448014901 1000000000 34608320262199 100000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (422962699/1000000000 : ℝ)^4209 ≤ (641483573027/2000000000000 : ℝ)^3185 := by
    have hnat : (422962699 : ℕ)^4209*2000000000000^3185 ≤ 641483573027^3185*1000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      422962699 1000000000 641483573027 2000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4209/1024 : ℝ)) 4209 3185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4353119447/10000000000 : ℝ), (448014901/1000000000 : ℝ), (422962699/1000000000 : ℝ)] ![(333175010629/1000000000000 : ℝ), (34608320262199/100000000000000 : ℝ), (641483573027/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4353119447/10000000000 : ℝ)|^4209 ≤ (333175010629/1000000000000 : ℝ)^3185
        have hw : |(4353119447/10000000000 : ℝ)|=(4353119447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(448014901/1000000000 : ℝ)|^4209 ≤ (34608320262199/100000000000000 : ℝ)^3185
        have hw : |(448014901/1000000000 : ℝ)|=(448014901/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(422962699/1000000000 : ℝ)|^4209 ≤ (641483573027/2000000000000 : ℝ)^3185
        have hw : |(422962699/1000000000 : ℝ)|=(422962699/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1225_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8417/2048 : ℝ) ≤ p) (hpb : p ≤ (4209/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37773923/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (141/1000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11453/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5729/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (881/6250 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (141/1000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11453/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (141/1000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11453/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (141/1000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11453/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (141/1000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11453/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (141/1000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11453/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (141/1000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11453/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11453/100000 : ℝ) ^ (8417/2048 : ℝ) ≤ (13560847276709121/100000000000000000000 : ℝ) := by
    have hpowers : (11453/100000 : ℝ)^8417 ≤ (13560847276709121/100000000000000000000 : ℝ)^2048 := by
      have hnat : (11453 : ℕ)^8417*100000000000000000000^2048 ≤ 13560847276709121^2048*100000^8417 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11453 100000 13560847276709121 100000000000000000000 8417 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11453/100000 : ℝ)) (X := (13560847276709121/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8417 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (141/1000 : ℝ) ^ (8417/2048 : ℝ) ≤ (497997195175543/1562500000000000000 : ℝ) := by
    have hpowers : (141/1000 : ℝ)^8417 ≤ (497997195175543/1562500000000000000 : ℝ)^2048 := by
      have hnat : (141 : ℕ)^8417*1562500000000000000^2048 ≤ 497997195175543^2048*1000^8417 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        141 1000 497997195175543 1562500000000000000 8417 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (141/1000 : ℝ)) (X := (497997195175543/1562500000000000000 : ℝ)) (by norm_num) (by norm_num) 8417 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013560847276709121/50000000000000000000 : ℝ) ≤ (2000131969898323/2000000000000000 : ℝ) ^ (8417/2048 : ℝ) := by
    have hpowers : (50013560847276709121/50000000000000000000 : ℝ)^2048 ≤ (2000131969898323/2000000000000000 : ℝ)^8417 := by
      have hnat : (50013560847276709121 : ℕ)^2048*2000000000000000^8417 ≤ 2000131969898323^8417*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013560847276709121 50000000000000000000 2000131969898323 2000000000000000 2048 8417 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000131969898323/2000000000000000 : ℝ)) (X := (50013560847276709121/50000000000000000000 : ℝ)) (by norm_num) 8417 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100045432667767943873/100000000000000000000 : ℝ) ≤ (10001105264513371/10000000000000000 : ℝ) ^ (8417/2048 : ℝ) := by
    have hpowers : (100045432667767943873/100000000000000000000 : ℝ)^2048 ≤ (10001105264513371/10000000000000000 : ℝ)^8417 := by
      have hnat : (100045432667767943873 : ℕ)^2048*10000000000000000^8417 ≤ 10001105264513371^8417*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100045432667767943873 100000000000000000000 10001105264513371 10000000000000000 2048 8417 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001105264513371/10000000000000000 : ℝ)) (X := (100045432667767943873/100000000000000000000 : ℝ)) (by norm_num) 8417 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (781747997195175543/781250000000000000 : ℝ) ≤ (10001550679535127/10000000000000000 : ℝ) ^ (8417/2048 : ℝ) := by
    have hpowers : (781747997195175543/781250000000000000 : ℝ)^2048 ≤ (10001550679535127/10000000000000000 : ℝ)^8417 := by
      have hnat : (781747997195175543 : ℕ)^2048*10000000000000000^8417 ≤ 10001550679535127^8417*781250000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        781747997195175543 781250000000000000 10001550679535127 10000000000000000 2048 8417 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001550679535127/10000000000000000 : ℝ)) (X := (781747997195175543/781250000000000000 : ℝ)) (by norm_num) 8417 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13560847276709121/100000000000000000000 : ℝ) ≤ ((26461543945115961969/26470000000000000000 : ℝ)+2*(111353755439/66175000000000 : ℝ)*(11453/100000 : ℝ))^(8417/2048 : ℝ) := by
    rw [show (26461543945115961969/26470000000000000000 : ℝ)+2*(111353755439/66175000000000 : ℝ)*(11453/100000 : ℝ)=(2000131969898323/2000000000000000 : ℝ) by norm_num, show 1+2*(13560847276709121/100000000000000000000 : ℝ)=(50013560847276709121/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(497997195175543/1562500000000000000 : ℝ)+(13560847276709121/100000000000000000000 : ℝ) ≤ ((26461543945115961969/26470000000000000000 : ℝ)+(111353755439/66175000000000 : ℝ)*((141/1000 : ℝ)+(11453/100000 : ℝ)))^(8417/2048 : ℝ) := by
    rw [show (26461543945115961969/26470000000000000000 : ℝ)+(111353755439/66175000000000 : ℝ)*((141/1000 : ℝ)+(11453/100000 : ℝ))=(10001105264513371/10000000000000000 : ℝ) by norm_num, show 1+(497997195175543/1562500000000000000 : ℝ)+(13560847276709121/100000000000000000000 : ℝ)=(100045432667767943873/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(497997195175543/1562500000000000000 : ℝ) ≤ ((26461543945115961969/26470000000000000000 : ℝ)+2*(111353755439/66175000000000 : ℝ)*(141/1000 : ℝ))^(8417/2048 : ℝ) := by
    rw [show (26461543945115961969/26470000000000000000 : ℝ)+2*(111353755439/66175000000000 : ℝ)*(141/1000 : ℝ)=(10001550679535127/10000000000000000 : ℝ) by norm_num, show 1+2*(497997195175543/1562500000000000000 : ℝ)=(781747997195175543/781250000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (26461543945115961969/26470000000000000000 : ℝ)*(X 1 0+X 2 0)+(111353755439/66175000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8417/2048 : ℝ)) (lo := (11453/100000 : ℝ)) (hi := (141/1000 : ℝ)) (c := (26461543945115961969/26470000000000000000 : ℝ)) (alpha := (111353755439/66175000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (26461543945115961969/26470000000000000000 : ℝ)*(X 0 1+X 2 1)+(111353755439/66175000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8417/2048 : ℝ)) (lo := (11453/100000 : ℝ)) (hi := (141/1000 : ℝ)) (c := (26461543945115961969/26470000000000000000 : ℝ)) (alpha := (111353755439/66175000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (26461543945115961969/26470000000000000000 : ℝ)*(X 0 2+X 1 2)+(111353755439/66175000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8417/2048 : ℝ)) (lo := (11453/100000 : ℝ)) (hi := (141/1000 : ℝ)) (c := (26461543945115961969/26470000000000000000 : ℝ)) (alpha := (111353755439/66175000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2127815533/10000000000 : ℝ)*X 0 0+(5391513957/10000000000 : ℝ)*X 0 1+(1053396463/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1225_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672198101/5000000000 : ℝ)*X 1 0+(-219096023/1000000000 : ℝ)*X 1 1+(1053396459/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1225_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((668049523/1250000000 : ℝ)*X 2 0+(5266982311/10000000000 : ℝ)*X 2 1+(-2190960233/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1225_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4353109897/10000000000 : ℝ)*X 0 0+(2114495379/5000000000 : ℝ)*X 0 1+(4480783013/10000000000 : ℝ)*X 0 2+(4353109897/10000000000 : ℝ)*X 1 0+(2114495379/5000000000 : ℝ)*X 1 1+(4480783013/10000000000 : ℝ)*X 1 2+(4353109897/10000000000 : ℝ)*X 2 0+(2114495379/5000000000 : ℝ)*X 2 1+(4480783013/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1225_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1063910117/5000000000 : ℝ)*X 0 0+(5267296931/10000000000 : ℝ)*X 0 1+(1347799551/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1225_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((132816449/250000000 : ℝ)*X 1 0+(-1033371581/5000000000 : ℝ)*X 1 1+(1078239883/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1225_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((332041161/625000000 : ℝ)*X 2 0+(2695599149/5000000000 : ℝ)*X 2 1+(-2066743847/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1225_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4353119447/10000000000 : ℝ)*X 0 0+(448014901/1000000000 : ℝ)*X 0 1+(422962699/1000000000 : ℝ)*X 0 2+(4353119447/10000000000 : ℝ)*X 1 0+(448014901/1000000000 : ℝ)*X 1 1+(422962699/1000000000 : ℝ)*X 1 2+(4353119447/10000000000 : ℝ)*X 2 0+(448014901/1000000000 : ℝ)*X 2 1+(422962699/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1225_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (190757517976567595297212743/66175000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (52929359/10000000000000 : ℝ)*(base19) + (238257873/50000000000000 : ℝ)*(base23) + (6876183/50000000000000 : ℝ)*(lower2) + (71679217/100000000000000 : ℝ)*(upper3) + (21561929/50000000000000 : ℝ)*(upper5) + (600082847008051/10000000000000 : ℝ)*(major0) + (600082847008051/10000000000000 : ℝ)*(major1) + (600082847008051/10000000000000 : ℝ)*(major2) + (4015051001558323/50000000000000 : ℝ)*(sp0) + (8030114578116527/100000000000000 : ℝ)*(sp1) + (8030114630894371/100000000000000 : ℝ)*(sp2) + (3971534578733913/100000000000000 : ℝ)*(sp3) + (409509171/3125000000000 : ℝ)*(sp4) + (7157929571/100000000000000 : ℝ)*(sp7) + (1985770868331743/50000000000000 : ℝ)*(f.failure) + (8030115107410117/100000000000000 : ℝ)*(f.sum) + (316924126697/41359375000000000000000000 : ℝ)*base65 + (2245074628363812419/264700000000000000000000000000000 : ℝ)*base67 + (710901083915487581/264700000000000000000000000000000 : ℝ)*base70 + (1289978467724012419/264700000000000000000000000000000 : ℝ)*base71 + (8553504242837/1323500000000000000000000000 : ℝ)*base73 + (1444696683935612419/264700000000000000000000000000000 : ℝ)*base75 + (5083857443017012419/264700000000000000000000000000000 : ℝ)*base77 + (6541285668326912419/264700000000000000000000000000000 : ℝ)*base79 + (758369219793/132350000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (23537789/1250000000000000000000 : ℝ)*base89 + (23537789/1250000000000000000000 : ℝ)*base91 + (23537789/1250000000000000000000 : ℝ)*base93 + (1/50000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (10054685808151193685159619641/1323500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1535959471/100000000000000 : ℝ)*(base19) + (2460451347/100000000000000 : ℝ)*(base23) + (10482221/3125000000000 : ℝ)*(upper3) + (65086413/100000000000000 : ℝ)*(lower4) + (6031329867207521/100000000000000 : ℝ)*(major0) + (6031329867207521/100000000000000 : ℝ)*(major1) + (6031329867207521/100000000000000 : ℝ)*(major2) + (108668737039/100000000000000 : ℝ)*(sp1) + (21566746209/25000000000000 : ℝ)*(sp2) + (3329372627/12500000000000 : ℝ)*(sp3) + (8070930936591779/100000000000000 : ℝ)*(sp4) + (8070820731895269/100000000000000 : ℝ)*(sp5) + (2017710552288899/25000000000000 : ℝ)*(sp6) + (997925477401871/25000000000000 : ℝ)*(sp7) + (7983457089177/200000000000 : ℝ)*(f.failure) + (8070930936591779/100000000000000 : ℝ)*(f.sum) + (5769714826207/6617500000000000000000000000 : ℝ)*base66 + (28985063791044631151/2647000000000000000000000000000000 : ℝ)*base68 + (59770648064393631151/2647000000000000000000000000000000 : ℝ)*base70 + (646818075891631151/2647000000000000000000000000000000 : ℝ)*base72 + (5211394408353/1654375000000000000000000000 : ℝ)*base74 + (69489974726321631151/2647000000000000000000000000000000 : ℝ)*base76 + (57304635461185631151/2647000000000000000000000000000000 : ℝ)*base78 + (30475540137729631151/2647000000000000000000000000000000 : ℝ)*base80 + (5140749461849/3308750000000000000000000000 : ℝ)*base81 + (81371/5000000000000000000 : ℝ)*base89 + (81371/5000000000000000000 : ℝ)*base91 + (81371/5000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1225_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8417/2048 : ℝ) ≤ p) (hpb : p ≤ (4209/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37773923/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (141/1000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11453/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5729/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (881/6250 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1225_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1225_s8_0 (p : ℝ) (hpa : (8417/2048 : ℝ) ≤ p) (hpb : p ≤ (4209/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2672193451/5000000000 : ℝ)*x 0 + (5267023457/10000000000 : ℝ)*x 1 + (-1095459023/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672193451/5000000000 : ℝ)^4209 ≤ (170677068667/390625000000 : ℝ)^3185 := by
    have hnat : (2672193451 : ℕ)^4209*390625000000^3185 ≤ 170677068667^3185*5000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672193451 5000000000 170677068667 390625000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5267023457/10000000000 : ℝ)^4209 ≤ (42859442168377/100000000000000 : ℝ)^3185 := by
    have hnat : (5267023457 : ℕ)^4209*100000000000000^3185 ≤ 42859442168377^3185*10000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267023457 10000000000 42859442168377 100000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1095459023/5000000000 : ℝ)^4209 ≤ (2689445647209/20000000000000 : ℝ)^3185 := by
    have hnat : (1095459023 : ℕ)^4209*20000000000000^3185 ≤ 2689445647209^3185*5000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1095459023 5000000000 2689445647209 20000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4209/1024 : ℝ)) 4209 3185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672193451/5000000000 : ℝ), (5267023457/10000000000 : ℝ), (-1095459023/5000000000 : ℝ)] ![(170677068667/390625000000 : ℝ), (42859442168377/100000000000000 : ℝ), (2689445647209/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672193451/5000000000 : ℝ)|^4209 ≤ (170677068667/390625000000 : ℝ)^3185
        have hw : |(2672193451/5000000000 : ℝ)|=(2672193451/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5267023457/10000000000 : ℝ)|^4209 ≤ (42859442168377/100000000000000 : ℝ)^3185
        have hw : |(5267023457/10000000000 : ℝ)|=(5267023457/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1095459023/5000000000 : ℝ)|^4209 ≤ (2689445647209/20000000000000 : ℝ)^3185
        have hw : |(-1095459023/5000000000 : ℝ)|=(1095459023/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1225_s8_1 (p : ℝ) (hpa : (8417/2048 : ℝ) ≤ p) (hpb : p ≤ (4209/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-265977523/1250000000 : ℝ)*x 0 + (5267336883/10000000000 : ℝ)*x 1 + (2695579293/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (265977523/1250000000 : ℝ)^4209 ≤ (12937824467523/100000000000000 : ℝ)^3185 := by
    have hnat : (265977523 : ℕ)^4209*100000000000000^3185 ≤ 12937824467523^3185*1250000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      265977523 1250000000 12937824467523 100000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5267336883/10000000000 : ℝ)^4209 ≤ (21431406317091/50000000000000 : ℝ)^3185 := by
    have hnat : (5267336883 : ℕ)^4209*50000000000000^3185 ≤ 21431406317091^3185*10000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267336883 10000000000 21431406317091 50000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2695579293/5000000000 : ℝ)^4209 ≤ (2762460179941/6250000000000 : ℝ)^3185 := by
    have hnat : (2695579293 : ℕ)^4209*6250000000000^3185 ≤ 2762460179941^3185*5000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695579293 5000000000 2762460179941 6250000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4209/1024 : ℝ)) 4209 3185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-265977523/1250000000 : ℝ), (5267336883/10000000000 : ℝ), (2695579293/5000000000 : ℝ)] ![(12937824467523/100000000000000 : ℝ), (21431406317091/50000000000000 : ℝ), (2762460179941/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-265977523/1250000000 : ℝ)|^4209 ≤ (12937824467523/100000000000000 : ℝ)^3185
        have hw : |(-265977523/1250000000 : ℝ)|=(265977523/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5267336883/10000000000 : ℝ)|^4209 ≤ (21431406317091/50000000000000 : ℝ)^3185
        have hw : |(5267336883/10000000000 : ℝ)|=(5267336883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2695579293/5000000000 : ℝ)|^4209 ≤ (2762460179941/6250000000000 : ℝ)^3185
        have hw : |(2695579293/5000000000 : ℝ)|=(2695579293/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1225_s8_2 (p : ℝ) (hpa : (8417/2048 : ℝ) ≤ p) (hpb : p ≤ (4209/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1062533927/2000000000 : ℝ)*x 0 + (-1033391459/5000000000 : ℝ)*x 1 + (1078231717/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062533927/2000000000 : ℝ)^4209 ≤ (2167549093931/5000000000000 : ℝ)^3185 := by
    have hnat : (1062533927 : ℕ)^4209*5000000000000^3185 ≤ 2167549093931^3185*2000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062533927 2000000000 2167549093931 5000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1033391459/5000000000 : ℝ)^4209 ≤ (1556206905193/12500000000000 : ℝ)^3185 := by
    have hnat : (1033391459 : ℕ)^4209*12500000000000^3185 ≤ 1556206905193^3185*5000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1033391459 5000000000 1556206905193 12500000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1078231717/2000000000 : ℝ)^4209 ≤ (22099681434111/50000000000000 : ℝ)^3185 := by
    have hnat : (1078231717 : ℕ)^4209*50000000000000^3185 ≤ 22099681434111^3185*2000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078231717 2000000000 22099681434111 50000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4209/1024 : ℝ)) 4209 3185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062533927/2000000000 : ℝ), (-1033391459/5000000000 : ℝ), (1078231717/2000000000 : ℝ)] ![(2167549093931/5000000000000 : ℝ), (1556206905193/12500000000000 : ℝ), (22099681434111/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062533927/2000000000 : ℝ)|^4209 ≤ (2167549093931/5000000000000 : ℝ)^3185
        have hw : |(1062533927/2000000000 : ℝ)|=(1062533927/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1033391459/5000000000 : ℝ)|^4209 ≤ (1556206905193/12500000000000 : ℝ)^3185
        have hw : |(-1033391459/5000000000 : ℝ)|=(1033391459/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1078231717/2000000000 : ℝ)|^4209 ≤ (22099681434111/50000000000000 : ℝ)^3185
        have hw : |(1078231717/2000000000 : ℝ)|=(1078231717/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1225_s8_3 (p : ℝ) (hpa : (8417/2048 : ℝ) ≤ p) (hpb : p ≤ (4209/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2656334817/5000000000 : ℝ)*x 0 + (2695579293/5000000000 : ℝ)*x 1 + (-2066782917/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656334817/5000000000 : ℝ)^4209 ≤ (43350981867837/100000000000000 : ℝ)^3185 := by
    have hnat : (2656334817 : ℕ)^4209*100000000000000^3185 ≤ 43350981867837^3185*5000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656334817 5000000000 43350981867837 100000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2695579293/5000000000 : ℝ)^4209 ≤ (2762460179941/6250000000000 : ℝ)^3185 := by
    have hnat : (2695579293 : ℕ)^4209*6250000000000^3185 ≤ 2762460179941^3185*5000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695579293 5000000000 2762460179941 6250000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2066782917/10000000000 : ℝ)^4209 ≤ (12449655233583/100000000000000 : ℝ)^3185 := by
    have hnat : (2066782917 : ℕ)^4209*100000000000000^3185 ≤ 12449655233583^3185*10000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2066782917 10000000000 12449655233583 100000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4209/1024 : ℝ)) 4209 3185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656334817/5000000000 : ℝ), (2695579293/5000000000 : ℝ), (-2066782917/10000000000 : ℝ)] ![(43350981867837/100000000000000 : ℝ), (2762460179941/6250000000000 : ℝ), (12449655233583/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656334817/5000000000 : ℝ)|^4209 ≤ (43350981867837/100000000000000 : ℝ)^3185
        have hw : |(2656334817/5000000000 : ℝ)|=(2656334817/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2695579293/5000000000 : ℝ)|^4209 ≤ (2762460179941/6250000000000 : ℝ)^3185
        have hw : |(2695579293/5000000000 : ℝ)|=(2695579293/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2066782917/10000000000 : ℝ)|^4209 ≤ (12449655233583/100000000000000 : ℝ)^3185
        have hw : |(-2066782917/10000000000 : ℝ)|=(2066782917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1225_s8_4 (p : ℝ) (hpa : (8417/2048 : ℝ) ≤ p) (hpb : p ≤ (4209/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4353121451/10000000000 : ℝ)*x 0 + (560008271/1250000000 : ℝ)*x 1 + (1057427339/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4353121451/10000000000 : ℝ)^4209 ≤ (4164690166527/12500000000000 : ℝ)^3185 := by
    have hnat : (4353121451 : ℕ)^4209*12500000000000^3185 ≤ 4164690166527^3185*10000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4353121451 10000000000 4164690166527 12500000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (560008271/1250000000 : ℝ)^4209 ≤ (2162967161293/6250000000000 : ℝ)^3185 := by
    have hnat : (560008271 : ℕ)^4209*6250000000000^3185 ≤ 2162967161293^3185*1250000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      560008271 1250000000 2162967161293 6250000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1057427339/2500000000 : ℝ)^4209 ≤ (32075004066241/100000000000000 : ℝ)^3185 := by
    have hnat : (1057427339 : ℕ)^4209*100000000000000^3185 ≤ 32075004066241^3185*2500000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1057427339 2500000000 32075004066241 100000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4209/1024 : ℝ)) 4209 3185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4353121451/10000000000 : ℝ), (560008271/1250000000 : ℝ), (1057427339/2500000000 : ℝ)] ![(4164690166527/12500000000000 : ℝ), (2162967161293/6250000000000 : ℝ), (32075004066241/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4353121451/10000000000 : ℝ)|^4209 ≤ (4164690166527/12500000000000 : ℝ)^3185
        have hw : |(4353121451/10000000000 : ℝ)|=(4353121451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(560008271/1250000000 : ℝ)|^4209 ≤ (2162967161293/6250000000000 : ℝ)^3185
        have hw : |(560008271/1250000000 : ℝ)|=(560008271/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1057427339/2500000000 : ℝ)|^4209 ≤ (32075004066241/100000000000000 : ℝ)^3185
        have hw : |(1057427339/2500000000 : ℝ)|=(1057427339/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1225_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8417/2048 : ℝ) ≤ p) (hpb : p ≤ (4209/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37773923/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (881/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5729/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (5729/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2819/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (881/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5729/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (881/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5729/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (881/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5729/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (881/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5729/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (881/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5729/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (881/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5729/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5729/50000 : ℝ) ^ (8417/2048 : ℝ) ≤ (1698149384735909/12500000000000000000 : ℝ) := by
    have hpowers : (5729/50000 : ℝ)^8417 ≤ (1698149384735909/12500000000000000000 : ℝ)^2048 := by
      have hnat : (5729 : ℕ)^8417*12500000000000000000^2048 ≤ 1698149384735909^2048*50000^8417 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5729 50000 1698149384735909 12500000000000000000 8417 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5729/50000 : ℝ)) (X := (1698149384735909/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 8417 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (881/6250 : ℝ) ^ (8417/2048 : ℝ) ≤ (31834676929507569/100000000000000000000 : ℝ) := by
    have hpowers : (881/6250 : ℝ)^8417 ≤ (31834676929507569/100000000000000000000 : ℝ)^2048 := by
      have hnat : (881 : ℕ)^8417*100000000000000000000^2048 ≤ 31834676929507569^2048*6250^8417 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        881 6250 31834676929507569 100000000000000000000 8417 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (881/6250 : ℝ)) (X := (31834676929507569/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8417 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (6251698149384735909/6250000000000000000 : ℝ) ≤ (10000661034095551/10000000000000000 : ℝ) ^ (8417/2048 : ℝ) := by
    have hpowers : (6251698149384735909/6250000000000000000 : ℝ)^2048 ≤ (10000661034095551/10000000000000000 : ℝ)^8417 := by
      have hnat : (6251698149384735909 : ℕ)^2048*10000000000000000^8417 ≤ 10000661034095551^8417*6250000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6251698149384735909 6250000000000000000 10000661034095551 10000000000000000 2048 8417 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000661034095551/10000000000000000 : ℝ)) (X := (6251698149384735909/6250000000000000000 : ℝ)) (by norm_num) 8417 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100045419872007394841/100000000000000000000 : ℝ) ≤ (10001104953277617/10000000000000000 : ℝ) ^ (8417/2048 : ℝ) := by
    have hpowers : (100045419872007394841/100000000000000000000 : ℝ)^2048 ≤ (10001104953277617/10000000000000000 : ℝ)^8417 := by
      have hnat : (100045419872007394841 : ℕ)^2048*10000000000000000^8417 ≤ 10001104953277617^8417*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100045419872007394841 100000000000000000000 10001104953277617 10000000000000000 2048 8417 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001104953277617/10000000000000000 : ℝ)) (X := (100045419872007394841/100000000000000000000 : ℝ)) (by norm_num) 8417 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50031834676929507569/50000000000000000000 : ℝ) ≤ (10001548872459683/10000000000000000 : ℝ) ^ (8417/2048 : ℝ) := by
    have hpowers : (50031834676929507569/50000000000000000000 : ℝ)^2048 ≤ (10001548872459683/10000000000000000 : ℝ)^8417 := by
      have hnat : (50031834676929507569 : ℕ)^2048*10000000000000000^8417 ≤ 10001548872459683^8417*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50031834676929507569 50000000000000000000 10001548872459683 10000000000000000 2048 8417 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001548872459683/10000000000000000 : ℝ)) (X := (50031834676929507569/50000000000000000000 : ℝ)) (by norm_num) 8417 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1698149384735909/12500000000000000000 : ℝ) ≤ ((13185785477983919541/13190000000000000000 : ℝ)+2*(221959591033/131900000000000 : ℝ)*(5729/50000 : ℝ))^(8417/2048 : ℝ) := by
    rw [show (13185785477983919541/13190000000000000000 : ℝ)+2*(221959591033/131900000000000 : ℝ)*(5729/50000 : ℝ)=(10000661034095551/10000000000000000 : ℝ) by norm_num, show 1+2*(1698149384735909/12500000000000000000 : ℝ)=(6251698149384735909/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(31834676929507569/100000000000000000000 : ℝ)+(1698149384735909/12500000000000000000 : ℝ) ≤ ((13185785477983919541/13190000000000000000 : ℝ)+(221959591033/131900000000000 : ℝ)*((881/6250 : ℝ)+(5729/50000 : ℝ)))^(8417/2048 : ℝ) := by
    rw [show (13185785477983919541/13190000000000000000 : ℝ)+(221959591033/131900000000000 : ℝ)*((881/6250 : ℝ)+(5729/50000 : ℝ))=(10001104953277617/10000000000000000 : ℝ) by norm_num, show 1+(31834676929507569/100000000000000000000 : ℝ)+(1698149384735909/12500000000000000000 : ℝ)=(100045419872007394841/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(31834676929507569/100000000000000000000 : ℝ) ≤ ((13185785477983919541/13190000000000000000 : ℝ)+2*(221959591033/131900000000000 : ℝ)*(881/6250 : ℝ))^(8417/2048 : ℝ) := by
    rw [show (13185785477983919541/13190000000000000000 : ℝ)+2*(221959591033/131900000000000 : ℝ)*(881/6250 : ℝ)=(10001548872459683/10000000000000000 : ℝ) by norm_num, show 1+2*(31834676929507569/100000000000000000000 : ℝ)=(50031834676929507569/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13185785477983919541/13190000000000000000 : ℝ)*(X 1 0+X 2 0)+(221959591033/131900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8417/2048 : ℝ)) (lo := (5729/50000 : ℝ)) (hi := (881/6250 : ℝ)) (c := (13185785477983919541/13190000000000000000 : ℝ)) (alpha := (221959591033/131900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13185785477983919541/13190000000000000000 : ℝ)*(X 0 1+X 2 1)+(221959591033/131900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8417/2048 : ℝ)) (lo := (5729/50000 : ℝ)) (hi := (881/6250 : ℝ)) (c := (13185785477983919541/13190000000000000000 : ℝ)) (alpha := (221959591033/131900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13185785477983919541/13190000000000000000 : ℝ)*(X 0 2+X 1 2)+(221959591033/131900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8417/2048 : ℝ)) (lo := (5729/50000 : ℝ)) (hi := (881/6250 : ℝ)) (c := (13185785477983919541/13190000000000000000 : ℝ)) (alpha := (221959591033/131900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((2672193451/5000000000 : ℝ)*X 2 0+(5267023457/10000000000 : ℝ)*X 2 1+(-1095459023/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1225_s8_0 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((-265977523/1250000000 : ℝ)*X 0 0+(5267336883/10000000000 : ℝ)*X 0 1+(2695579293/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1225_s8_1 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1062533927/2000000000 : ℝ)*X 1 0+(-1033391459/5000000000 : ℝ)*X 1 1+(1078231717/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1225_s8_2 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2656334817/5000000000 : ℝ)*X 2 0+(2695579293/5000000000 : ℝ)*X 2 1+(-2066782917/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1225_s8_3 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((4353121451/10000000000 : ℝ)*X 0 0+(560008271/1250000000 : ℝ)*X 0 1+(1057427339/2500000000 : ℝ)*X 0 2+(4353121451/10000000000 : ℝ)*X 1 0+(560008271/1250000000 : ℝ)*X 1 1+(1057427339/2500000000 : ℝ)*X 1 2+(4353121451/10000000000 : ℝ)*X 2 0+(560008271/1250000000 : ℝ)*X 2 1+(1057427339/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1225_s8_4 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(lower0) + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6298931419978210269909/824375000000000000000000000 : ℝ) := by norm_num
    linear_combination (1373326737/100000000000000 : ℝ)*(base19) + (46640873/3125000000000 : ℝ)*(base23) + (95818379/20000000000000 : ℝ)*(lower1) + (153044989/100000000000000 : ℝ)*(upper3) + (13744063/25000000000000 : ℝ)*(lower4) + (156847939/100000000000000 : ℝ)*(upper5) + (6035184163682163/100000000000000 : ℝ)*(major0) + (6035184163682163/100000000000000 : ℝ)*(major1) + (6035184163682163/100000000000000 : ℝ)*(major2) + (180272459/6250000000000 : ℝ)*(sp0) + (8076088630418533/100000000000000 : ℝ)*(sp1) + (8076087257091797/100000000000000 : ℝ)*(sp2) + (4038042126775627/50000000000000 : ℝ)*(sp3) + (99856986056263/2500000000000 : ℝ)*(sp4) + (99856986056263/2500000000000 : ℝ)*(f.failure) + (8076088630418533/100000000000000 : ℝ)*(f.sum) + (42374616340181/6595000000000000000000000000 : ℝ)*base66 + (41650079519445747183/1319000000000000000000000000000000 : ℝ)*base67 + (2256633486975252817/1319000000000000000000000000000000 : ℝ)*base70 + (142668690474941747183/1319000000000000000000000000000000 : ℝ)*base71 + (19670818750549/6595000000000000000000000000 : ℝ)*base73 + (290554622171308252817/1319000000000000000000000000000000 : ℝ)*base76 + (18427003341890747183/1319000000000000000000000000000000 : ℝ)*base77 + (14619313099301252817/1319000000000000000000000000000000 : ℝ)*base80 + (18814512573531/6595000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (354749/62500000000000000000 : ℝ)*base89 + (354749/62500000000000000000 : ℝ)*base91 + (354749/62500000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1225_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8417/2048 : ℝ) ≤ p) (hpb : p ≤ (4209/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37773923/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (881/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5729/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5729/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2819/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1225_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1225_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8417/2048 : ℝ) ≤ p) (hpb : p ≤ (4209/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37773923/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14123/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11431/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5729/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2819/20000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1225_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1225_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1225_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8417/2048 : ℝ) ≤ p) (hpb : p ≤ (4209/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37773923/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14123/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11431/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5729/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2819/20000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1225_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
