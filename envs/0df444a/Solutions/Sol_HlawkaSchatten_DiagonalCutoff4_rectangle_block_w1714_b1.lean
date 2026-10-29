-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1714_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:54:45.302773+00:00
-- url     : https://prove2.me/submissions/e4a48a72-2368-4266-b8ae-34f1a029f7bc

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
theorem support_rectangle_w1714_s3_0 (p : ℝ) (hpa : (5327/1024 : ℝ) ≤ p) (hpb : p ≤ (5335/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-698877213/5000000000 : ℝ)*x 0 + (1366869887/2500000000 : ℝ)*x 1 + (5138778323/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (698877213/5000000000 : ℝ)^5335 ≤ (8758776663781/100000000000000 : ℝ)^4311 := by
    have hnat : (698877213 : ℕ)^5335*100000000000000^4311 ≤ 8758776663781^4311*5000000000^5335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      698877213 5000000000 8758776663781 100000000000000 5335 4311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1366869887/2500000000 : ℝ)^5335 ≤ (5921248245533/12500000000000 : ℝ)^4311 := by
    have hnat : (1366869887 : ℕ)^5335*12500000000000^4311 ≤ 5921248245533^4311*2500000000^5335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1366869887 2500000000 5921248245533 12500000000000 5335 4311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5138778323/10000000000 : ℝ)^5335 ≤ (21935618682123/50000000000000 : ℝ)^4311 := by
    have hnat : (5138778323 : ℕ)^5335*50000000000000^4311 ≤ 21935618682123^4311*10000000000^5335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5138778323 10000000000 21935618682123 50000000000000 5335 4311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5335/1024 : ℝ)) 5335 4311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-698877213/5000000000 : ℝ), (1366869887/2500000000 : ℝ), (5138778323/10000000000 : ℝ)] ![(8758776663781/100000000000000 : ℝ), (5921248245533/12500000000000 : ℝ), (21935618682123/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-698877213/5000000000 : ℝ)|^5335 ≤ (8758776663781/100000000000000 : ℝ)^4311
        have hw : |(-698877213/5000000000 : ℝ)|=(698877213/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1366869887/2500000000 : ℝ)|^5335 ≤ (5921248245533/12500000000000 : ℝ)^4311
        have hw : |(1366869887/2500000000 : ℝ)|=(1366869887/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5138778323/10000000000 : ℝ)|^5335 ≤ (21935618682123/50000000000000 : ℝ)^4311
        have hw : |(5138778323/10000000000 : ℝ)|=(5138778323/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1714_s3_1 (p : ℝ) (hpa : (5327/1024 : ℝ) ≤ p) (hpb : p ≤ (5335/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (133554307/250000000 : ℝ)*x 0 + (-1568138527/10000000000 : ℝ)*x 1 + (1284694581/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (133554307/250000000 : ℝ)^5335 ≤ (23015065123329/50000000000000 : ℝ)^4311 := by
    have hnat : (133554307 : ℕ)^5335*50000000000000^4311 ≤ 23015065123329^4311*250000000^5335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      133554307 250000000 23015065123329 50000000000000 5335 4311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1568138527/10000000000 : ℝ)^5335 ≤ (5049316186161/50000000000000 : ℝ)^4311 := by
    have hnat : (1568138527 : ℕ)^5335*50000000000000^4311 ≤ 5049316186161^4311*10000000000^5335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1568138527 10000000000 5049316186161 50000000000000 5335 4311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1284694581/2500000000 : ℝ)^5335 ≤ (43871237374811/100000000000000 : ℝ)^4311 := by
    have hnat : (1284694581 : ℕ)^5335*100000000000000^4311 ≤ 43871237374811^4311*2500000000^5335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1284694581 2500000000 43871237374811 100000000000000 5335 4311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5335/1024 : ℝ)) 5335 4311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(133554307/250000000 : ℝ), (-1568138527/10000000000 : ℝ), (1284694581/2500000000 : ℝ)] ![(23015065123329/50000000000000 : ℝ), (5049316186161/50000000000000 : ℝ), (43871237374811/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(133554307/250000000 : ℝ)|^5335 ≤ (23015065123329/50000000000000 : ℝ)^4311
        have hw : |(133554307/250000000 : ℝ)|=(133554307/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1568138527/10000000000 : ℝ)|^5335 ≤ (5049316186161/50000000000000 : ℝ)^4311
        have hw : |(-1568138527/10000000000 : ℝ)|=(1568138527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1284694581/2500000000 : ℝ)|^5335 ≤ (43871237374811/100000000000000 : ℝ)^4311
        have hw : |(1284694581/2500000000 : ℝ)|=(1284694581/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1714_s3_2 (p : ℝ) (hpa : (5327/1024 : ℝ) ≤ p) (hpb : p ≤ (5335/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (133554307/250000000 : ℝ)*x 0 + (1284694581/2500000000 : ℝ)*x 1 + (-784069263/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (133554307/250000000 : ℝ)^5335 ≤ (23015065123329/50000000000000 : ℝ)^4311 := by
    have hnat : (133554307 : ℕ)^5335*50000000000000^4311 ≤ 23015065123329^4311*250000000^5335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      133554307 250000000 23015065123329 50000000000000 5335 4311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1284694581/2500000000 : ℝ)^5335 ≤ (43871237374811/100000000000000 : ℝ)^4311 := by
    have hnat : (1284694581 : ℕ)^5335*100000000000000^4311 ≤ 43871237374811^4311*2500000000^5335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1284694581 2500000000 43871237374811 100000000000000 5335 4311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (784069263/5000000000 : ℝ)^5335 ≤ (157791130693/1562500000000 : ℝ)^4311 := by
    have hnat : (784069263 : ℕ)^5335*1562500000000^4311 ≤ 157791130693^4311*5000000000^5335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      784069263 5000000000 157791130693 1562500000000 5335 4311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5335/1024 : ℝ)) 5335 4311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(133554307/250000000 : ℝ), (1284694581/2500000000 : ℝ), (-784069263/5000000000 : ℝ)] ![(23015065123329/50000000000000 : ℝ), (43871237374811/100000000000000 : ℝ), (157791130693/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(133554307/250000000 : ℝ)|^5335 ≤ (23015065123329/50000000000000 : ℝ)^4311
        have hw : |(133554307/250000000 : ℝ)|=(133554307/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1284694581/2500000000 : ℝ)|^5335 ≤ (43871237374811/100000000000000 : ℝ)^4311
        have hw : |(1284694581/2500000000 : ℝ)|=(1284694581/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-784069263/5000000000 : ℝ)|^5335 ≤ (157791130693/1562500000000 : ℝ)^4311
        have hw : |(-784069263/5000000000 : ℝ)|=(784069263/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1714_s3_3 (p : ℝ) (hpa : (5327/1024 : ℝ) ≤ p) (hpb : p ≤ (5335/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (512450707/1250000000 : ℝ)*x 0 + (3636417087/10000000000 : ℝ)*x 1 + (4598098591/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (512450707/1250000000 : ℝ)^5335 ≤ (33170802372261/100000000000000 : ℝ)^4311 := by
    have hnat : (512450707 : ℕ)^5335*100000000000000^4311 ≤ 33170802372261^4311*1250000000^5335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      512450707 1250000000 33170802372261 100000000000000 5335 4311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3636417087/10000000000 : ℝ)^5335 ≤ (28596947543341/100000000000000 : ℝ)^4311 := by
    have hnat : (3636417087 : ℕ)^5335*100000000000000^4311 ≤ 28596947543341^4311*10000000000^5335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3636417087 10000000000 28596947543341 100000000000000 5335 4311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4598098591/10000000000 : ℝ)^5335 ≤ (38232250073019/100000000000000 : ℝ)^4311 := by
    have hnat : (4598098591 : ℕ)^5335*100000000000000^4311 ≤ 38232250073019^4311*10000000000^5335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4598098591 10000000000 38232250073019 100000000000000 5335 4311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5335/1024 : ℝ)) 5335 4311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(512450707/1250000000 : ℝ), (3636417087/10000000000 : ℝ), (4598098591/10000000000 : ℝ)] ![(33170802372261/100000000000000 : ℝ), (28596947543341/100000000000000 : ℝ), (38232250073019/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(512450707/1250000000 : ℝ)|^5335 ≤ (33170802372261/100000000000000 : ℝ)^4311
        have hw : |(512450707/1250000000 : ℝ)|=(512450707/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3636417087/10000000000 : ℝ)|^5335 ≤ (28596947543341/100000000000000 : ℝ)^4311
        have hw : |(3636417087/10000000000 : ℝ)|=(3636417087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4598098591/10000000000 : ℝ)|^5335 ≤ (38232250073019/100000000000000 : ℝ)^4311
        have hw : |(4598098591/10000000000 : ℝ)|=(4598098591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1714_s3_4 (p : ℝ) (hpa : (5327/1024 : ℝ) ≤ p) (hpb : p ≤ (5335/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1397902837/10000000000 : ℝ)*x 0 + (5142431371/10000000000 : ℝ)*x 1 + (5463771961/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1397902837/10000000000 : ℝ)^5335 ≤ (2189981892903/25000000000000 : ℝ)^4311 := by
    have hnat : (1397902837 : ℕ)^5335*25000000000000^4311 ≤ 2189981892903^4311*10000000000^5335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1397902837 10000000000 2189981892903 25000000000000 5335 4311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5142431371/10000000000 : ℝ)^5335 ≤ (43909835687447/100000000000000 : ℝ)^4311 := by
    have hnat : (5142431371 : ℕ)^5335*100000000000000^4311 ≤ 43909835687447^4311*10000000000^5335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5142431371 10000000000 43909835687447 100000000000000 5335 4311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5463771961/10000000000 : ℝ)^5335 ≤ (4733023672181/10000000000000 : ℝ)^4311 := by
    have hnat : (5463771961 : ℕ)^5335*10000000000000^4311 ≤ 4733023672181^4311*10000000000^5335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5463771961 10000000000 4733023672181 10000000000000 5335 4311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5335/1024 : ℝ)) 5335 4311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1397902837/10000000000 : ℝ), (5142431371/10000000000 : ℝ), (5463771961/10000000000 : ℝ)] ![(2189981892903/25000000000000 : ℝ), (43909835687447/100000000000000 : ℝ), (4733023672181/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1397902837/10000000000 : ℝ)|^5335 ≤ (2189981892903/25000000000000 : ℝ)^4311
        have hw : |(-1397902837/10000000000 : ℝ)|=(1397902837/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5142431371/10000000000 : ℝ)|^5335 ≤ (43909835687447/100000000000000 : ℝ)^4311
        have hw : |(5142431371/10000000000 : ℝ)|=(5142431371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5463771961/10000000000 : ℝ)|^5335 ≤ (4733023672181/10000000000000 : ℝ)^4311
        have hw : |(5463771961/10000000000 : ℝ)|=(5463771961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1714_s3_5 (p : ℝ) (hpa : (5327/1024 : ℝ) ≤ p) (hpb : p ≤ (5335/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1050836393/2000000000 : ℝ)*x 0 + (-1243144567/10000000000 : ℝ)*x 1 + (109275447/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1050836393/2000000000 : ℝ)^5335 ≤ (22546864904797/50000000000000 : ℝ)^4311 := by
    have hnat : (1050836393 : ℕ)^5335*50000000000000^4311 ≤ 22546864904797^4311*2000000000^5335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1050836393 2000000000 22546864904797 50000000000000 5335 4311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1243144567/10000000000 : ℝ)^5335 ≤ (7576029281091/100000000000000 : ℝ)^4311 := by
    have hnat : (1243144567 : ℕ)^5335*100000000000000^4311 ≤ 7576029281091^4311*10000000000^5335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1243144567 10000000000 7576029281091 100000000000000 5335 4311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (109275447/200000000 : ℝ)^5335 ≤ (11832560222991/25000000000000 : ℝ)^4311 := by
    have hnat : (109275447 : ℕ)^5335*25000000000000^4311 ≤ 11832560222991^4311*200000000^5335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      109275447 200000000 11832560222991 25000000000000 5335 4311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5335/1024 : ℝ)) 5335 4311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1050836393/2000000000 : ℝ), (-1243144567/10000000000 : ℝ), (109275447/200000000 : ℝ)] ![(22546864904797/50000000000000 : ℝ), (7576029281091/100000000000000 : ℝ), (11832560222991/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1050836393/2000000000 : ℝ)|^5335 ≤ (22546864904797/50000000000000 : ℝ)^4311
        have hw : |(1050836393/2000000000 : ℝ)|=(1050836393/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1243144567/10000000000 : ℝ)|^5335 ≤ (7576029281091/100000000000000 : ℝ)^4311
        have hw : |(-1243144567/10000000000 : ℝ)|=(1243144567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(109275447/200000000 : ℝ)|^5335 ≤ (11832560222991/25000000000000 : ℝ)^4311
        have hw : |(109275447/200000000 : ℝ)|=(109275447/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1714_s3_6 (p : ℝ) (hpa : (5327/1024 : ℝ) ≤ p) (hpb : p ≤ (5335/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5254181923/10000000000 : ℝ)*x 0 + (5463772223/10000000000 : ℝ)*x 1 + (-1243144807/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5254181923/10000000000 : ℝ)^5335 ≤ (4509372936351/10000000000000 : ℝ)^4311 := by
    have hnat : (5254181923 : ℕ)^5335*10000000000000^4311 ≤ 4509372936351^4311*10000000000^5335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5254181923 10000000000 4509372936351 10000000000000 5335 4311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5463772223/10000000000 : ℝ)^5335 ≤ (94660479061/200000000000 : ℝ)^4311 := by
    have hnat : (5463772223 : ℕ)^5335*200000000000^4311 ≤ 94660479061^4311*10000000000^5335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5463772223 10000000000 94660479061 200000000000 5335 4311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1243144807/10000000000 : ℝ)^5335 ≤ (7576031091129/100000000000000 : ℝ)^4311 := by
    have hnat : (1243144807 : ℕ)^5335*100000000000000^4311 ≤ 7576031091129^4311*10000000000^5335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1243144807 10000000000 7576031091129 100000000000000 5335 4311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5335/1024 : ℝ)) 5335 4311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5254181923/10000000000 : ℝ), (5463772223/10000000000 : ℝ), (-1243144807/10000000000 : ℝ)] ![(4509372936351/10000000000000 : ℝ), (94660479061/200000000000 : ℝ), (7576031091129/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5254181923/10000000000 : ℝ)|^5335 ≤ (4509372936351/10000000000000 : ℝ)^4311
        have hw : |(5254181923/10000000000 : ℝ)|=(5254181923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5463772223/10000000000 : ℝ)|^5335 ≤ (94660479061/200000000000 : ℝ)^4311
        have hw : |(5463772223/10000000000 : ℝ)|=(5463772223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1243144807/10000000000 : ℝ)|^5335 ≤ (7576031091129/100000000000000 : ℝ)^4311
        have hw : |(-1243144807/10000000000 : ℝ)|=(1243144807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1714_s3_7 (p : ℝ) (hpa : (5327/1024 : ℝ) ≤ p) (hpb : p ≤ (5335/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1025009901/2500000000 : ℝ)*x 0 + (4587411577/10000000000 : ℝ)*x 1 + (3647263209/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1025009901/2500000000 : ℝ)^5335 ≤ (1658757380451/5000000000000 : ℝ)^4311 := by
    have hnat : (1025009901 : ℕ)^5335*5000000000000^4311 ≤ 1658757380451^4311*2500000000^5335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1025009901 2500000000 1658757380451 5000000000000 5335 4311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4587411577/10000000000 : ℝ)^5335 ≤ (2382644559039/6250000000000 : ℝ)^4311 := by
    have hnat : (4587411577 : ℕ)^5335*6250000000000^4311 ≤ 2382644559039^4311*10000000000^5335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4587411577 10000000000 2382644559039 6250000000000 5335 4311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3647263209/10000000000 : ℝ)^5335 ≤ (1435126971797/5000000000000 : ℝ)^4311 := by
    have hnat : (3647263209 : ℕ)^5335*5000000000000^4311 ≤ 1435126971797^4311*10000000000^5335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3647263209 10000000000 1435126971797 5000000000000 5335 4311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5335/1024 : ℝ)) 5335 4311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1025009901/2500000000 : ℝ), (4587411577/10000000000 : ℝ), (3647263209/10000000000 : ℝ)] ![(1658757380451/5000000000000 : ℝ), (2382644559039/6250000000000 : ℝ), (1435126971797/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1025009901/2500000000 : ℝ)|^5335 ≤ (1658757380451/5000000000000 : ℝ)^4311
        have hw : |(1025009901/2500000000 : ℝ)|=(1025009901/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4587411577/10000000000 : ℝ)|^5335 ≤ (2382644559039/6250000000000 : ℝ)^4311
        have hw : |(4587411577/10000000000 : ℝ)|=(4587411577/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3647263209/10000000000 : ℝ)|^5335 ≤ (1435126971797/5000000000000 : ℝ)^4311
        have hw : |(3647263209/10000000000 : ℝ)|=(3647263209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1714_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5327/1024 : ℝ) ≤ p) (hpb : p ≤ (5335/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (196285051/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8537/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10033/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5021/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2133/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8537/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10033/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8537/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10033/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8537/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10033/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8537/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10033/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8537/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10033/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8537/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10033/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10033/100000 : ℝ) ^ (5327/1024 : ℝ) ≤ (638696976377899/100000000000000000000 : ℝ) := by
    have hpowers : (10033/100000 : ℝ)^5327 ≤ (638696976377899/100000000000000000000 : ℝ)^1024 := by
      have hnat : (10033 : ℕ)^5327*100000000000000000000^1024 ≤ 638696976377899^1024*100000^5327 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10033 100000 638696976377899 100000000000000000000 5327 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10033/100000 : ℝ)) (X := (638696976377899/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5327 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8537/50000 : ℝ) ^ (5327/1024 : ℝ) ≤ (2537664298805107/25000000000000000000 : ℝ) := by
    have hpowers : (8537/50000 : ℝ)^5327 ≤ (2537664298805107/25000000000000000000 : ℝ)^1024 := by
      have hnat : (8537 : ℕ)^5327*25000000000000000000^1024 ≤ 2537664298805107^1024*50000^5327 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8537 50000 2537664298805107 25000000000000000000 5327 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8537/50000 : ℝ)) (X := (2537664298805107/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5327 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000638696976377899/50000000000000000000 : ℝ) ≤ (5000012277498209/5000000000000000 : ℝ) ^ (5327/1024 : ℝ) := by
    have hpowers : (50000638696976377899/50000000000000000000 : ℝ)^1024 ≤ (5000012277498209/5000000000000000 : ℝ)^5327 := by
      have hnat : (50000638696976377899 : ℕ)^1024*5000000000000000^5327 ≤ 5000012277498209^5327*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000638696976377899 50000000000000000000 5000012277498209 5000000000000000 1024 5327 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000012277498209/5000000000000000 : ℝ)) (X := (50000638696976377899/50000000000000000000 : ℝ)) (by norm_num) 5327 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100010789354171598327/100000000000000000000 : ℝ) ≤ (5000103696426271/5000000000000000 : ℝ) ^ (5327/1024 : ℝ) := by
    have hpowers : (100010789354171598327/100000000000000000000 : ℝ)^1024 ≤ (5000103696426271/5000000000000000 : ℝ)^5327 := by
      have hnat : (100010789354171598327 : ℕ)^1024*5000000000000000^5327 ≤ 5000103696426271^5327*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100010789354171598327 100000000000000000000 5000103696426271 5000000000000000 1024 5327 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000103696426271/5000000000000000 : ℝ)) (X := (100010789354171598327/100000000000000000000 : ℝ)) (by norm_num) 5327 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12502537664298805107/12500000000000000000 : ℝ) ≤ (5000195115354333/5000000000000000 : ℝ) ^ (5327/1024 : ℝ) := by
    have hpowers : (12502537664298805107/12500000000000000000 : ℝ)^1024 ≤ (5000195115354333/5000000000000000 : ℝ)^5327 := by
      have hnat : (12502537664298805107 : ℕ)^1024*5000000000000000^5327 ≤ 5000195115354333^5327*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12502537664298805107 12500000000000000000 5000195115354333 5000000000000000 1024 5327 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000195115354333/5000000000000000 : ℝ)) (X := (12502537664298805107/12500000000000000000 : ℝ)) (by norm_num) 5327 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(638696976377899/100000000000000000000 : ℝ) ≤ ((35203252033654397477/35205000000000000000 : ℝ)+2*(45709464031/176025000000000 : ℝ)*(10033/100000 : ℝ))^(5327/1024 : ℝ) := by
    rw [show (35203252033654397477/35205000000000000000 : ℝ)+2*(45709464031/176025000000000 : ℝ)*(10033/100000 : ℝ)=(5000012277498209/5000000000000000 : ℝ) by norm_num, show 1+2*(638696976377899/100000000000000000000 : ℝ)=(50000638696976377899/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2537664298805107/25000000000000000000 : ℝ)+(638696976377899/100000000000000000000 : ℝ) ≤ ((35203252033654397477/35205000000000000000 : ℝ)+(45709464031/176025000000000 : ℝ)*((8537/50000 : ℝ)+(10033/100000 : ℝ)))^(5327/1024 : ℝ) := by
    rw [show (35203252033654397477/35205000000000000000 : ℝ)+(45709464031/176025000000000 : ℝ)*((8537/50000 : ℝ)+(10033/100000 : ℝ))=(5000103696426271/5000000000000000 : ℝ) by norm_num, show 1+(2537664298805107/25000000000000000000 : ℝ)+(638696976377899/100000000000000000000 : ℝ)=(100010789354171598327/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2537664298805107/25000000000000000000 : ℝ) ≤ ((35203252033654397477/35205000000000000000 : ℝ)+2*(45709464031/176025000000000 : ℝ)*(8537/50000 : ℝ))^(5327/1024 : ℝ) := by
    rw [show (35203252033654397477/35205000000000000000 : ℝ)+2*(45709464031/176025000000000 : ℝ)*(8537/50000 : ℝ)=(5000195115354333/5000000000000000 : ℝ) by norm_num, show 1+2*(2537664298805107/25000000000000000000 : ℝ)=(12502537664298805107/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (35203252033654397477/35205000000000000000 : ℝ)*(X 1 0+X 2 0)+(45709464031/176025000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5327/1024 : ℝ)) (lo := (10033/100000 : ℝ)) (hi := (8537/50000 : ℝ)) (c := (35203252033654397477/35205000000000000000 : ℝ)) (alpha := (45709464031/176025000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (35203252033654397477/35205000000000000000 : ℝ)*(X 0 1+X 2 1)+(45709464031/176025000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5327/1024 : ℝ)) (lo := (10033/100000 : ℝ)) (hi := (8537/50000 : ℝ)) (c := (35203252033654397477/35205000000000000000 : ℝ)) (alpha := (45709464031/176025000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (35203252033654397477/35205000000000000000 : ℝ)*(X 0 2+X 1 2)+(45709464031/176025000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5327/1024 : ℝ)) (lo := (10033/100000 : ℝ)) (hi := (8537/50000 : ℝ)) (c := (35203252033654397477/35205000000000000000 : ℝ)) (alpha := (45709464031/176025000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-698877213/5000000000 : ℝ)*X 0 0+(1366869887/2500000000 : ℝ)*X 0 1+(5138778323/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1714_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((133554307/250000000 : ℝ)*X 1 0+(-1568138527/10000000000 : ℝ)*X 1 1+(1284694581/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1714_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((133554307/250000000 : ℝ)*X 2 0+(1284694581/2500000000 : ℝ)*X 2 1+(-784069263/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1714_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((512450707/1250000000 : ℝ)*X 0 0+(3636417087/10000000000 : ℝ)*X 0 1+(4598098591/10000000000 : ℝ)*X 0 2+(512450707/1250000000 : ℝ)*X 1 0+(3636417087/10000000000 : ℝ)*X 1 1+(4598098591/10000000000 : ℝ)*X 1 2+(512450707/1250000000 : ℝ)*X 2 0+(3636417087/10000000000 : ℝ)*X 2 1+(4598098591/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1714_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1397902837/10000000000 : ℝ)*X 0 0+(5142431371/10000000000 : ℝ)*X 0 1+(5463771961/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1714_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1050836393/2000000000 : ℝ)*X 1 0+(-1243144567/10000000000 : ℝ)*X 1 1+(109275447/200000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1714_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5254181923/10000000000 : ℝ)*X 2 0+(5463772223/10000000000 : ℝ)*X 2 1+(-1243144807/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1714_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1025009901/2500000000 : ℝ)*X 0 0+(4587411577/10000000000 : ℝ)*X 0 1+(3647263209/10000000000 : ℝ)*X 0 2+(1025009901/2500000000 : ℝ)*X 1 0+(4587411577/10000000000 : ℝ)*X 1 1+(3647263209/10000000000 : ℝ)*X 1 2+(1025009901/2500000000 : ℝ)*X 2 0+(4587411577/10000000000 : ℝ)*X 2 1+(3647263209/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1714_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6950273475090144008073/1173500000000000000000000000 : ℝ) := by norm_num
    linear_combination (433668187/50000000000000 : ℝ)*(base19) + (407478233/50000000000000 : ℝ)*(base23) + (27982249/100000000000000 : ℝ)*(lower2) + (142981009/100000000000000 : ℝ)*(upper3) + (26530639/25000000000000 : ℝ)*(upper5) + (408214527158853/20000000000000 : ℝ)*(major0) + (408214527158853/20000000000000 : ℝ)*(major1) + (408214527158853/20000000000000 : ℝ)*(major2) + (3042285200322087/100000000000000 : ℝ)*(sp0) + (1521146458186993/50000000000000 : ℝ)*(sp1) + (1521146484376947/50000000000000 : ℝ)*(sp2) + (1039848113289247/100000000000000 : ℝ)*(sp3) + (8583388273/100000000000000 : ℝ)*(sp4) + (3177166013/100000000000000 : ℝ)*(sp7) + (51992564522763/5000000000000 : ℝ)*(f.failure) + (76057344592759/2500000000000 : ℝ)*(f.sum) + (10273275065463/2347000000000000000000000000 : ℝ)*base66 + (158632120359704627/234700000000000000000000000000000 : ℝ)*base67 + (830128723154404627/234700000000000000000000000000000 : ℝ)*base69 + (128125106739204627/234700000000000000000000000000000 : ℝ)*base71 + (893273695193/586750000000000000000000000 : ℝ)*base74 + (166629505392595373/234700000000000000000000000000000 : ℝ)*base76 + (469550234588795373/234700000000000000000000000000000 : ℝ)*base78 + (203722312026195373/234700000000000000000000000000000 : ℝ)*base80 + (4493779251887/1173500000000000000000000000 : ℝ)*base81 + (1115913/500000000000000000000 : ℝ)*base89 + (1115913/500000000000000000000 : ℝ)*base91 + (1115913/500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1675913665151401028867915557/293375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (32752521/4000000000000 : ℝ)*(base19) + (25003207/3125000000000 : ℝ)*(base23) + (126786721/50000000000000 : ℝ)*(lower1) + (461141/100000000000000 : ℝ)*(upper2) + (47782739/20000000000000 : ℝ)*(upper3) + (791333/1250000000000 : ℝ)*(upper5) + (2087805854247041/100000000000000 : ℝ)*(major0) + (2087805854247041/100000000000000 : ℝ)*(major1) + (2087805854247041/100000000000000 : ℝ)*(major2) + (78936687/25000000000000 : ℝ)*(sp2) + (1555975687514551/50000000000000 : ℝ)*(sp4) + (3111950556216077/100000000000000 : ℝ)*(sp5) + (311195025917973/10000000000000 : ℝ)*(sp6) + (132957517880911/12500000000000 : ℝ)*(sp7) + (132957517880911/12500000000000 : ℝ)*(f.failure) + (1555975687514551/50000000000000 : ℝ)*(f.sum) + (119075343987203/17602500000000000000000000000 : ℝ)*base66 + (14129460326549684443/3520500000000000000000000000000000 : ℝ)*base68 + (1435326608567684443/3520500000000000000000000000000000 : ℝ)*base70 + (16290460244449184443/3520500000000000000000000000000000 : ℝ)*base72 + (147589977516901/35205000000000000000000000000 : ℝ)*base74 + (1833591673908315557/3520500000000000000000000000000000 : ℝ)*base75 + (38903740437911684443/3520500000000000000000000000000000 : ℝ)*base78 + (27760031188199684443/3520500000000000000000000000000000 : ℝ)*base80 + (24543100477057/17602500000000000000000000000 : ℝ)*base81 + (15061461/1250000000000000000000 : ℝ)*base89 + (15061461/1250000000000000000000 : ℝ)*base91 + (15061461/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1714_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5327/1024 : ℝ) ≤ p) (hpb : p ≤ (5335/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (196285051/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8537/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10033/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5021/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2133/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1714_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1714_box_0 (p : ℝ) (hpa : (5327/1024 : ℝ) ≤ p) (hpb : p ≤ (5335/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1082201391/10000000000 : ℝ)*x 0 + (2707559889/5000000000 : ℝ)*x 1 + (135378001/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1082201391/10000000000 : ℝ)^5335 ≤ (1595384860429/25000000000000 : ℝ)^4311 := by
    have hnat : (1082201391 : ℕ)^5335*25000000000000^4311 ≤ 1595384860429^4311*10000000000^5335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082201391 10000000000 1595384860429 25000000000000 5335 4311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2707559889/5000000000 : ℝ)^5335 ≤ (23404614435577/50000000000000 : ℝ)^4311 := by
    have hnat : (2707559889 : ℕ)^5335*50000000000000^4311 ≤ 23404614435577^4311*5000000000^5335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2707559889 5000000000 23404614435577 50000000000000 5335 4311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (135378001/250000000 : ℝ)^5335 ≤ (46809231673883/100000000000000 : ℝ)^4311 := by
    have hnat : (135378001 : ℕ)^5335*100000000000000^4311 ≤ 46809231673883^4311*250000000^5335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135378001 250000000 46809231673883 100000000000000 5335 4311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5335/1024 : ℝ)) 5335 4311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1082201391/10000000000 : ℝ), (2707559889/5000000000 : ℝ), (135378001/250000000 : ℝ)] ![(1595384860429/25000000000000 : ℝ), (23404614435577/50000000000000 : ℝ), (46809231673883/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1082201391/10000000000 : ℝ)|^5335 ≤ (1595384860429/25000000000000 : ℝ)^4311
        have hw : |(-1082201391/10000000000 : ℝ)|=(1082201391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2707559889/5000000000 : ℝ)|^5335 ≤ (23404614435577/50000000000000 : ℝ)^4311
        have hw : |(2707559889/5000000000 : ℝ)|=(2707559889/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(135378001/250000000 : ℝ)|^5335 ≤ (46809231673883/100000000000000 : ℝ)^4311
        have hw : |(135378001/250000000 : ℝ)|=(135378001/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1714_box_1 (p : ℝ) (hpa : (5327/1024 : ℝ) ≤ p) (hpb : p ≤ (5335/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5225200153/10000000000 : ℝ)*x 0 + (-1351909293/10000000000 : ℝ)*x 1 + (5415119953/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5225200153/10000000000 : ℝ)^5335 ≤ (22393057237211/50000000000000 : ℝ)^4311 := by
    have hnat : (5225200153 : ℕ)^5335*50000000000000^4311 ≤ 22393057237211^4311*10000000000^5335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5225200153 10000000000 22393057237211 50000000000000 5335 4311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1351909293/10000000000 : ℝ)^5335 ≤ (1050581845563/12500000000000 : ℝ)^4311 := by
    have hnat : (1351909293 : ℕ)^5335*12500000000000^4311 ≤ 1050581845563^4311*10000000000^5335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1351909293 10000000000 1050581845563 12500000000000 5335 4311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5415119953/10000000000 : ℝ)^5335 ≤ (23404615371603/50000000000000 : ℝ)^4311 := by
    have hnat : (5415119953 : ℕ)^5335*50000000000000^4311 ≤ 23404615371603^4311*10000000000^5335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5415119953 10000000000 23404615371603 50000000000000 5335 4311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5335/1024 : ℝ)) 5335 4311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5225200153/10000000000 : ℝ), (-1351909293/10000000000 : ℝ), (5415119953/10000000000 : ℝ)] ![(22393057237211/50000000000000 : ℝ), (1050581845563/12500000000000 : ℝ), (23404615371603/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5225200153/10000000000 : ℝ)|^5335 ≤ (22393057237211/50000000000000 : ℝ)^4311
        have hw : |(5225200153/10000000000 : ℝ)|=(5225200153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1351909293/10000000000 : ℝ)|^5335 ≤ (1050581845563/12500000000000 : ℝ)^4311
        have hw : |(-1351909293/10000000000 : ℝ)|=(1351909293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5415119953/10000000000 : ℝ)|^5335 ≤ (23404615371603/50000000000000 : ℝ)^4311
        have hw : |(5415119953/10000000000 : ℝ)|=(5415119953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1714_box_2 (p : ℝ) (hpa : (5327/1024 : ℝ) ≤ p) (hpb : p ≤ (5335/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2612599837/5000000000 : ℝ)*x 0 + (5415120311/10000000000 : ℝ)*x 1 + (-84494341/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2612599837/5000000000 : ℝ)^5335 ≤ (44786109393619/100000000000000 : ℝ)^4311 := by
    have hnat : (2612599837 : ℕ)^5335*100000000000000^4311 ≤ 44786109393619^4311*5000000000^5335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2612599837 5000000000 44786109393619 100000000000000 5335 4311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5415120311/10000000000 : ℝ)^5335 ≤ (46809234572889/100000000000000 : ℝ)^4311 := by
    have hnat : (5415120311 : ℕ)^5335*100000000000000^4311 ≤ 46809234572889^4311*10000000000^5335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5415120311 10000000000 46809234572889 100000000000000 5335 4311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (84494341/625000000 : ℝ)^5335 ≤ (8404656018559/100000000000000 : ℝ)^4311 := by
    have hnat : (84494341 : ℕ)^5335*100000000000000^4311 ≤ 8404656018559^4311*625000000^5335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84494341 625000000 8404656018559 100000000000000 5335 4311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5335/1024 : ℝ)) 5335 4311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2612599837/5000000000 : ℝ), (5415120311/10000000000 : ℝ), (-84494341/625000000 : ℝ)] ![(44786109393619/100000000000000 : ℝ), (46809234572889/100000000000000 : ℝ), (8404656018559/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2612599837/5000000000 : ℝ)|^5335 ≤ (44786109393619/100000000000000 : ℝ)^4311
        have hw : |(2612599837/5000000000 : ℝ)|=(2612599837/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5415120311/10000000000 : ℝ)|^5335 ≤ (46809234572889/100000000000000 : ℝ)^4311
        have hw : |(5415120311/10000000000 : ℝ)|=(5415120311/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-84494341/625000000 : ℝ)|^5335 ≤ (8404656018559/100000000000000 : ℝ)^4311
        have hw : |(-84494341/625000000 : ℝ)|=(84494341/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1714_box_3 (p : ℝ) (hpa : (5327/1024 : ℝ) ≤ p) (hpb : p ≤ (5335/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (448104727/1000000000 : ℝ)*x 0 + (1965166963/5000000000 : ℝ)*x 1 + (1965166939/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (448104727/1000000000 : ℝ)^5335 ≤ (37031477765261/100000000000000 : ℝ)^4311 := by
    have hnat : (448104727 : ℕ)^5335*100000000000000^4311 ≤ 37031477765261^4311*1000000000^5335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      448104727 1000000000 37031477765261 100000000000000 5335 4311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1965166963/5000000000 : ℝ)^5335 ≤ (31484261350211/100000000000000 : ℝ)^4311 := by
    have hnat : (1965166963 : ℕ)^5335*100000000000000^4311 ≤ 31484261350211^4311*5000000000^5335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1965166963 5000000000 31484261350211 100000000000000 5335 4311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1965166939/5000000000 : ℝ)^5335 ≤ (3148426087437/10000000000000 : ℝ)^4311 := by
    have hnat : (1965166939 : ℕ)^5335*10000000000000^4311 ≤ 3148426087437^4311*5000000000^5335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1965166939 5000000000 3148426087437 10000000000000 5335 4311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5335/1024 : ℝ)) 5335 4311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(448104727/1000000000 : ℝ), (1965166963/5000000000 : ℝ), (1965166939/5000000000 : ℝ)] ![(37031477765261/100000000000000 : ℝ), (31484261350211/100000000000000 : ℝ), (3148426087437/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(448104727/1000000000 : ℝ)|^5335 ≤ (37031477765261/100000000000000 : ℝ)^4311
        have hw : |(448104727/1000000000 : ℝ)|=(448104727/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1965166963/5000000000 : ℝ)|^5335 ≤ (31484261350211/100000000000000 : ℝ)^4311
        have hw : |(1965166963/5000000000 : ℝ)|=(1965166963/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1965166939/5000000000 : ℝ)|^5335 ≤ (3148426087437/10000000000000 : ℝ)^4311
        have hw : |(1965166939/5000000000 : ℝ)|=(1965166939/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1714_box_4 (p : ℝ) (hpa : (5327/1024 : ℝ) ≤ p) (hpb : p ≤ (5335/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1733881941/10000000000 : ℝ)*x 0 + (5177637133/10000000000 : ℝ)*x 1 + (2588818527/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1733881941/10000000000 : ℝ)^5335 ≤ (571784519149/5000000000000 : ℝ)^4311 := by
    have hnat : (1733881941 : ℕ)^5335*5000000000000^4311 ≤ 571784519149^4311*10000000000^5335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1733881941 10000000000 571784519149 5000000000000 5335 4311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5177637133/10000000000 : ℝ)^5335 ≤ (44282155220159/100000000000000 : ℝ)^4311 := by
    have hnat : (5177637133 : ℕ)^5335*100000000000000^4311 ≤ 44282155220159^4311*10000000000^5335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5177637133 10000000000 44282155220159 100000000000000 5335 4311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2588818527/5000000000 : ℝ)^5335 ≤ (2767634649001/6250000000000 : ℝ)^4311 := by
    have hnat : (2588818527 : ℕ)^5335*6250000000000^4311 ≤ 2767634649001^4311*5000000000^5335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2588818527 5000000000 2767634649001 6250000000000 5335 4311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5335/1024 : ℝ)) 5335 4311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1733881941/10000000000 : ℝ), (5177637133/10000000000 : ℝ), (2588818527/5000000000 : ℝ)] ![(571784519149/5000000000000 : ℝ), (44282155220159/100000000000000 : ℝ), (2767634649001/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1733881941/10000000000 : ℝ)|^5335 ≤ (571784519149/5000000000000 : ℝ)^4311
        have hw : |(-1733881941/10000000000 : ℝ)|=(1733881941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5177637133/10000000000 : ℝ)|^5335 ≤ (44282155220159/100000000000000 : ℝ)^4311
        have hw : |(5177637133/10000000000 : ℝ)|=(5177637133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2588818527/5000000000 : ℝ)|^5335 ≤ (2767634649001/6250000000000 : ℝ)^4311
        have hw : |(2588818527/5000000000 : ℝ)|=(2588818527/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1714_box_5 (p : ℝ) (hpa : (5327/1024 : ℝ) ≤ p) (hpb : p ≤ (5335/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2693051079/5000000000 : ℝ)*x 0 + (-291357477/2000000000 : ℝ)*x 1 + (2588818401/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2693051079/5000000000 : ℝ)^5335 ≤ (46499012474487/100000000000000 : ℝ)^4311 := by
    have hnat : (2693051079 : ℕ)^5335*100000000000000^4311 ≤ 46499012474487^4311*5000000000^5335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2693051079 5000000000 46499012474487 100000000000000 5335 4311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (291357477/2000000000 : ℝ)^5335 ≤ (576177237009/6250000000000 : ℝ)^4311 := by
    have hnat : (291357477 : ℕ)^5335*6250000000000^4311 ≤ 576177237009^4311*2000000000^5335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      291357477 2000000000 576177237009 6250000000000 5335 4311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2588818401/5000000000 : ℝ)^5335 ≤ (1771286068673/4000000000000 : ℝ)^4311 := by
    have hnat : (2588818401 : ℕ)^5335*4000000000000^4311 ≤ 1771286068673^4311*5000000000^5335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2588818401 5000000000 1771286068673 4000000000000 5335 4311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5335/1024 : ℝ)) 5335 4311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2693051079/5000000000 : ℝ), (-291357477/2000000000 : ℝ), (2588818401/5000000000 : ℝ)] ![(46499012474487/100000000000000 : ℝ), (576177237009/6250000000000 : ℝ), (1771286068673/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2693051079/5000000000 : ℝ)|^5335 ≤ (46499012474487/100000000000000 : ℝ)^4311
        have hw : |(2693051079/5000000000 : ℝ)|=(2693051079/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-291357477/2000000000 : ℝ)|^5335 ≤ (576177237009/6250000000000 : ℝ)^4311
        have hw : |(-291357477/2000000000 : ℝ)|=(291357477/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2588818401/5000000000 : ℝ)|^5335 ≤ (1771286068673/4000000000000 : ℝ)^4311
        have hw : |(2588818401/5000000000 : ℝ)|=(2588818401/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1714_box_6 (p : ℝ) (hpa : (5327/1024 : ℝ) ≤ p) (hpb : p ≤ (5335/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5386101817/10000000000 : ℝ)*x 0 + (2588818583/5000000000 : ℝ)*x 1 + (-1456787359/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5386101817/10000000000 : ℝ)^5335 ≤ (46499008831313/100000000000000 : ℝ)^4311 := by
    have hnat : (5386101817 : ℕ)^5335*100000000000000^4311 ≤ 46499008831313^4311*10000000000^5335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5386101817 10000000000 46499008831313 100000000000000 5335 4311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2588818583/5000000000 : ℝ)^5335 ≤ (22141077784717/50000000000000 : ℝ)^4311 := by
    have hnat : (2588818583 : ℕ)^5335*50000000000000^4311 ≤ 22141077784717^4311*5000000000^5335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2588818583 5000000000 22141077784717 50000000000000 5335 4311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1456787359/10000000000 : ℝ)^5335 ≤ (9218835588529/100000000000000 : ℝ)^4311 := by
    have hnat : (1456787359 : ℕ)^5335*100000000000000^4311 ≤ 9218835588529^4311*10000000000^5335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1456787359 10000000000 9218835588529 100000000000000 5335 4311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5335/1024 : ℝ)) 5335 4311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5386101817/10000000000 : ℝ), (2588818583/5000000000 : ℝ), (-1456787359/10000000000 : ℝ)] ![(46499008831313/100000000000000 : ℝ), (22141077784717/50000000000000 : ℝ), (9218835588529/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5386101817/10000000000 : ℝ)|^5335 ≤ (46499008831313/100000000000000 : ℝ)^4311
        have hw : |(5386101817/10000000000 : ℝ)|=(5386101817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2588818583/5000000000 : ℝ)|^5335 ≤ (22141077784717/50000000000000 : ℝ)^4311
        have hw : |(2588818583/5000000000 : ℝ)|=(2588818583/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1456787359/10000000000 : ℝ)|^5335 ≤ (9218835588529/100000000000000 : ℝ)^4311
        have hw : |(-1456787359/10000000000 : ℝ)|=(1456787359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1714_box_7 (p : ℝ) (hpa : (5327/1024 : ℝ) ≤ p) (hpb : p ≤ (5335/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1851155283/5000000000 : ℝ)*x 0 + (4318881401/10000000000 : ℝ)*x 1 + (431888099/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1851155283/5000000000 : ℝ)^5335 ≤ (5847919417387/20000000000000 : ℝ)^4311 := by
    have hnat : (1851155283 : ℕ)^5335*20000000000000^4311 ≤ 5847919417387^4311*5000000000^5335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1851155283 5000000000 5847919417387 20000000000000 5335 4311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4318881401/10000000000 : ℝ)^5335 ≤ (17690101764891/50000000000000 : ℝ)^4311 := by
    have hnat : (4318881401 : ℕ)^5335*50000000000000^4311 ≤ 17690101764891^4311*10000000000^5335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4318881401 10000000000 17690101764891 50000000000000 5335 4311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (431888099/1000000000 : ℝ)^5335 ≤ (35380199363129/100000000000000 : ℝ)^4311 := by
    have hnat : (431888099 : ℕ)^5335*100000000000000^4311 ≤ 35380199363129^4311*1000000000^5335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      431888099 1000000000 35380199363129 100000000000000 5335 4311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5335/1024 : ℝ)) 5335 4311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1851155283/5000000000 : ℝ), (4318881401/10000000000 : ℝ), (431888099/1000000000 : ℝ)] ![(5847919417387/20000000000000 : ℝ), (17690101764891/50000000000000 : ℝ), (35380199363129/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1851155283/5000000000 : ℝ)|^5335 ≤ (5847919417387/20000000000000 : ℝ)^4311
        have hw : |(1851155283/5000000000 : ℝ)|=(1851155283/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4318881401/10000000000 : ℝ)|^5335 ≤ (17690101764891/50000000000000 : ℝ)^4311
        have hw : |(4318881401/10000000000 : ℝ)|=(4318881401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(431888099/1000000000 : ℝ)|^5335 ≤ (35380199363129/100000000000000 : ℝ)^4311
        have hw : |(431888099/1000000000 : ℝ)|=(431888099/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1714_box_8 (p : ℝ) (hpa : (5327/1024 : ℝ) ≤ p) (hpb : p ≤ (5335/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-199207941/1250000000 : ℝ)*x 0 + (625269849/1250000000 : ℝ)*x 1 + (5457698347/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (199207941/1250000000 : ℝ)^5335 ≤ (10302447129183/100000000000000 : ℝ)^4311 := by
    have hnat : (199207941 : ℕ)^5335*100000000000000^4311 ≤ 10302447129183^4311*1250000000^5335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      199207941 1250000000 10302447129183 100000000000000 5335 4311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (625269849/1250000000 : ℝ)^5335 ≤ (42432417826731/100000000000000 : ℝ)^4311 := by
    have hnat : (625269849 : ℕ)^5335*100000000000000^4311 ≤ 42432417826731^4311*1250000000^5335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      625269849 1250000000 42432417826731 100000000000000 5335 4311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5457698347/10000000000 : ℝ)^5335 ≤ (738517734683/1562500000000 : ℝ)^4311 := by
    have hnat : (5457698347 : ℕ)^5335*1562500000000^4311 ≤ 738517734683^4311*10000000000^5335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5457698347 10000000000 738517734683 1562500000000 5335 4311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5335/1024 : ℝ)) 5335 4311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-199207941/1250000000 : ℝ), (625269849/1250000000 : ℝ), (5457698347/10000000000 : ℝ)] ![(10302447129183/100000000000000 : ℝ), (42432417826731/100000000000000 : ℝ), (738517734683/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-199207941/1250000000 : ℝ)|^5335 ≤ (10302447129183/100000000000000 : ℝ)^4311
        have hw : |(-199207941/1250000000 : ℝ)|=(199207941/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(625269849/1250000000 : ℝ)|^5335 ≤ (42432417826731/100000000000000 : ℝ)^4311
        have hw : |(625269849/1250000000 : ℝ)|=(625269849/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5457698347/10000000000 : ℝ)|^5335 ≤ (738517734683/1562500000000 : ℝ)^4311
        have hw : |(5457698347/10000000000 : ℝ)|=(5457698347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1714_box_9 (p : ℝ) (hpa : (5327/1024 : ℝ) ≤ p) (hpb : p ≤ (5335/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5196371453/10000000000 : ℝ)*x 0 + (-666168439/5000000000 : ℝ)*x 1 + (5457698931/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5196371453/10000000000 : ℝ)^5335 ≤ (11120131522053/25000000000000 : ℝ)^4311 := by
    have hnat : (5196371453 : ℕ)^5335*25000000000000^4311 ≤ 11120131522053^4311*10000000000^5335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5196371453 10000000000 11120131522053 25000000000000 5335 4311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (666168439/5000000000 : ℝ)^5335 ≤ (1031791576639/12500000000000 : ℝ)^4311 := by
    have hnat : (666168439 : ℕ)^5335*12500000000000^4311 ≤ 1031791576639^4311*5000000000^5335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      666168439 5000000000 1031791576639 12500000000000 5335 4311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5457698931/10000000000 : ℝ)^5335 ≤ (945302825573/2000000000000 : ℝ)^4311 := by
    have hnat : (5457698931 : ℕ)^5335*2000000000000^4311 ≤ 945302825573^4311*10000000000^5335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5457698931 10000000000 945302825573 2000000000000 5335 4311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5335/1024 : ℝ)) 5335 4311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5196371453/10000000000 : ℝ), (-666168439/5000000000 : ℝ), (5457698931/10000000000 : ℝ)] ![(11120131522053/25000000000000 : ℝ), (1031791576639/12500000000000 : ℝ), (945302825573/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5196371453/10000000000 : ℝ)|^5335 ≤ (11120131522053/25000000000000 : ℝ)^4311
        have hw : |(5196371453/10000000000 : ℝ)|=(5196371453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-666168439/5000000000 : ℝ)|^5335 ≤ (1031791576639/12500000000000 : ℝ)^4311
        have hw : |(-666168439/5000000000 : ℝ)|=(666168439/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5457698931/10000000000 : ℝ)|^5335 ≤ (945302825573/2000000000000 : ℝ)^4311
        have hw : |(5457698931/10000000000 : ℝ)|=(5457698931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1714_box_10 (p : ℝ) (hpa : (5327/1024 : ℝ) ≤ p) (hpb : p ≤ (5335/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1039274677/2000000000 : ℝ)*x 0 + (5457697321/10000000000 : ℝ)*x 1 + (-66616823/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1039274677/2000000000 : ℝ)^5335 ≤ (22240273277113/50000000000000 : ℝ)^4311 := by
    have hnat : (1039274677 : ℕ)^5335*50000000000000^4311 ≤ 22240273277113^4311*2000000000^5335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1039274677 2000000000 22240273277113 50000000000000 5335 4311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5457697321/10000000000 : ℝ)^5335 ≤ (23632562011851/50000000000000 : ℝ)^4311 := by
    have hnat : (5457697321 : ℕ)^5335*50000000000000^4311 ≤ 23632562011851^4311*10000000000^5335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5457697321 10000000000 23632562011851 50000000000000 5335 4311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (66616823/500000000 : ℝ)^5335 ≤ (1650865881663/20000000000000 : ℝ)^4311 := by
    have hnat : (66616823 : ℕ)^5335*20000000000000^4311 ≤ 1650865881663^4311*500000000^5335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66616823 500000000 1650865881663 20000000000000 5335 4311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5335/1024 : ℝ)) 5335 4311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1039274677/2000000000 : ℝ), (5457697321/10000000000 : ℝ), (-66616823/500000000 : ℝ)] ![(22240273277113/50000000000000 : ℝ), (23632562011851/50000000000000 : ℝ), (1650865881663/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1039274677/2000000000 : ℝ)|^5335 ≤ (22240273277113/50000000000000 : ℝ)^4311
        have hw : |(1039274677/2000000000 : ℝ)|=(1039274677/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5457697321/10000000000 : ℝ)|^5335 ≤ (23632562011851/50000000000000 : ℝ)^4311
        have hw : |(5457697321/10000000000 : ℝ)|=(5457697321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-66616823/500000000 : ℝ)|^5335 ≤ (1650865881663/20000000000000 : ℝ)^4311
        have hw : |(-66616823/500000000 : ℝ)|=(66616823/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1714_box_11 (p : ℝ) (hpa : (5327/1024 : ℝ) ≤ p) (hpb : p ≤ (5335/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4615693173/10000000000 : ℝ)*x 0 + (1930243451/5000000000 : ℝ)*x 1 + (6176779/16000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4615693173/10000000000 : ℝ)^5335 ≤ (4801672179557/12500000000000 : ℝ)^4311 := by
    have hnat : (4615693173 : ℕ)^5335*12500000000000^4311 ≤ 4801672179557^4311*10000000000^5335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4615693173 10000000000 4801672179557 12500000000000 5335 4311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1930243451/5000000000 : ℝ)^5335 ≤ (30793311408529/100000000000000 : ℝ)^4311 := by
    have hnat : (1930243451 : ℕ)^5335*100000000000000^4311 ≤ 30793311408529^4311*5000000000^5335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1930243451 5000000000 30793311408529 100000000000000 5335 4311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6176779/16000000 : ℝ)^5335 ≤ (30793311142007/100000000000000 : ℝ)^4311 := by
    have hnat : (6176779 : ℕ)^5335*100000000000000^4311 ≤ 30793311142007^4311*16000000^5335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6176779 16000000 30793311142007 100000000000000 5335 4311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5335/1024 : ℝ)) 5335 4311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4615693173/10000000000 : ℝ), (1930243451/5000000000 : ℝ), (6176779/16000000 : ℝ)] ![(4801672179557/12500000000000 : ℝ), (30793311408529/100000000000000 : ℝ), (30793311142007/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4615693173/10000000000 : ℝ)|^5335 ≤ (4801672179557/12500000000000 : ℝ)^4311
        have hw : |(4615693173/10000000000 : ℝ)|=(4615693173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1930243451/5000000000 : ℝ)|^5335 ≤ (30793311408529/100000000000000 : ℝ)^4311
        have hw : |(1930243451/5000000000 : ℝ)|=(1930243451/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6176779/16000000 : ℝ)|^5335 ≤ (30793311142007/100000000000000 : ℝ)^4311
        have hw : |(6176779/16000000 : ℝ)|=(6176779/16000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1714_box_12 (p : ℝ) (hpa : (5327/1024 : ℝ) ≤ p) (hpb : p ≤ (5335/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1216852731/10000000000 : ℝ)*x 0 + (2791184793/5000000000 : ℝ)*x 1 + (644069803/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1216852731/10000000000 : ℝ)^5335 ≤ (3689120822231/50000000000000 : ℝ)^4311 := by
    have hnat : (1216852731 : ℕ)^5335*50000000000000^4311 ≤ 3689120822231^4311*10000000000^5335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1216852731 10000000000 3689120822231 50000000000000 5335 4311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2791184793/5000000000 : ℝ)^5335 ≤ (48604885555939/100000000000000 : ℝ)^4311 := by
    have hnat : (2791184793 : ℕ)^5335*100000000000000^4311 ≤ 48604885555939^4311*5000000000^5335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2791184793 5000000000 48604885555939 100000000000000 5335 4311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (644069803/1250000000 : ℝ)^5335 ≤ (44016872780169/100000000000000 : ℝ)^4311 := by
    have hnat : (644069803 : ℕ)^5335*100000000000000^4311 ≤ 44016872780169^4311*1250000000^5335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      644069803 1250000000 44016872780169 100000000000000 5335 4311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5335/1024 : ℝ)) 5335 4311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1216852731/10000000000 : ℝ), (2791184793/5000000000 : ℝ), (644069803/1250000000 : ℝ)] ![(3689120822231/50000000000000 : ℝ), (48604885555939/100000000000000 : ℝ), (44016872780169/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1216852731/10000000000 : ℝ)|^5335 ≤ (3689120822231/50000000000000 : ℝ)^4311
        have hw : |(-1216852731/10000000000 : ℝ)|=(1216852731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2791184793/5000000000 : ℝ)|^5335 ≤ (48604885555939/100000000000000 : ℝ)^4311
        have hw : |(2791184793/5000000000 : ℝ)|=(2791184793/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(644069803/1250000000 : ℝ)|^5335 ≤ (44016872780169/100000000000000 : ℝ)^4311
        have hw : |(644069803/1250000000 : ℝ)|=(644069803/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1714_box_13 (p : ℝ) (hpa : (5327/1024 : ℝ) ≤ p) (hpb : p ≤ (5335/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5403125297/10000000000 : ℝ)*x 0 + (-733710379/5000000000 : ℝ)*x 1 + (2576278897/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5403125297/10000000000 : ℝ)^5335 ≤ (1867238096599/4000000000000 : ℝ)^4311 := by
    have hnat : (5403125297 : ℕ)^5335*4000000000000^4311 ≤ 1867238096599^4311*10000000000^5335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5403125297 10000000000 1867238096599 4000000000000 5335 4311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (733710379/5000000000 : ℝ)^5335 ≤ (9302181451347/100000000000000 : ℝ)^4311 := by
    have hnat : (733710379 : ℕ)^5335*100000000000000^4311 ≤ 9302181451347^4311*5000000000^5335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      733710379 5000000000 9302181451347 100000000000000 5335 4311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2576278897/5000000000 : ℝ)^5335 ≤ (22008433059939/50000000000000 : ℝ)^4311 := by
    have hnat : (2576278897 : ℕ)^5335*50000000000000^4311 ≤ 22008433059939^4311*5000000000^5335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2576278897 5000000000 22008433059939 50000000000000 5335 4311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5335/1024 : ℝ)) 5335 4311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5403125297/10000000000 : ℝ), (-733710379/5000000000 : ℝ), (2576278897/5000000000 : ℝ)] ![(1867238096599/4000000000000 : ℝ), (9302181451347/100000000000000 : ℝ), (22008433059939/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5403125297/10000000000 : ℝ)|^5335 ≤ (1867238096599/4000000000000 : ℝ)^4311
        have hw : |(5403125297/10000000000 : ℝ)|=(5403125297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-733710379/5000000000 : ℝ)|^5335 ≤ (9302181451347/100000000000000 : ℝ)^4311
        have hw : |(-733710379/5000000000 : ℝ)|=(733710379/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2576278897/5000000000 : ℝ)|^5335 ≤ (22008433059939/50000000000000 : ℝ)^4311
        have hw : |(2576278897/5000000000 : ℝ)|=(2576278897/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1714_box_14 (p : ℝ) (hpa : (5327/1024 : ℝ) ≤ p) (hpb : p ≤ (5335/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2701562543/5000000000 : ℝ)*x 0 + (2576278847/5000000000 : ℝ)*x 1 + (-1467421181/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2701562543/5000000000 : ℝ)^5335 ≤ (11670237539751/25000000000000 : ℝ)^4311 := by
    have hnat : (2701562543 : ℕ)^5335*25000000000000^4311 ≤ 11670237539751^4311*5000000000^5335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2701562543 5000000000 11670237539751 25000000000000 5335 4311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2576278847/5000000000 : ℝ)^5335 ≤ (44016865062689/100000000000000 : ℝ)^4311 := by
    have hnat : (2576278847 : ℕ)^5335*100000000000000^4311 ≤ 44016865062689^4311*5000000000^5335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2576278847 5000000000 44016865062689 100000000000000 5335 4311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1467421181/10000000000 : ℝ)^5335 ≤ (4651092384867/50000000000000 : ℝ)^4311 := by
    have hnat : (1467421181 : ℕ)^5335*50000000000000^4311 ≤ 4651092384867^4311*10000000000^5335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1467421181 10000000000 4651092384867 50000000000000 5335 4311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5335/1024 : ℝ)) 5335 4311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2701562543/5000000000 : ℝ), (2576278847/5000000000 : ℝ), (-1467421181/10000000000 : ℝ)] ![(11670237539751/25000000000000 : ℝ), (44016865062689/100000000000000 : ℝ), (4651092384867/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2701562543/5000000000 : ℝ)|^5335 ≤ (11670237539751/25000000000000 : ℝ)^4311
        have hw : |(2701562543/5000000000 : ℝ)|=(2701562543/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2576278847/5000000000 : ℝ)|^5335 ≤ (44016865062689/100000000000000 : ℝ)^4311
        have hw : |(2576278847/5000000000 : ℝ)|=(2576278847/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1467421181/10000000000 : ℝ)|^5335 ≤ (4651092384867/50000000000000 : ℝ)^4311
        have hw : |(-1467421181/10000000000 : ℝ)|=(1467421181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1714_box_15 (p : ℝ) (hpa : (5327/1024 : ℝ) ≤ p) (hpb : p ≤ (5335/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1808544659/5000000000 : ℝ)*x 0 + (2179901497/5000000000 : ℝ)*x 1 + (4359801011/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1808544659/5000000000 : ℝ)^5335 ≤ (14204484233619/50000000000000 : ℝ)^4311 := by
    have hnat : (1808544659 : ℕ)^5335*50000000000000^4311 ≤ 14204484233619^4311*5000000000^5335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1808544659 5000000000 14204484233619 50000000000000 5335 4311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2179901497/5000000000 : ℝ)^5335 ≤ (7159105166417/20000000000000 : ℝ)^4311 := by
    have hnat : (2179901497 : ℕ)^5335*20000000000000^4311 ≤ 7159105166417^4311*5000000000^5335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2179901497 5000000000 7159105166417 20000000000000 5335 4311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4359801011/10000000000 : ℝ)^5335 ≤ (17897752841833/50000000000000 : ℝ)^4311 := by
    have hnat : (4359801011 : ℕ)^5335*50000000000000^4311 ≤ 17897752841833^4311*10000000000^5335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4359801011 10000000000 17897752841833 50000000000000 5335 4311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5335/1024 : ℝ)) 5335 4311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1808544659/5000000000 : ℝ), (2179901497/5000000000 : ℝ), (4359801011/10000000000 : ℝ)] ![(14204484233619/50000000000000 : ℝ), (7159105166417/20000000000000 : ℝ), (17897752841833/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1808544659/5000000000 : ℝ)|^5335 ≤ (14204484233619/50000000000000 : ℝ)^4311
        have hw : |(1808544659/5000000000 : ℝ)|=(1808544659/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2179901497/5000000000 : ℝ)|^5335 ≤ (7159105166417/20000000000000 : ℝ)^4311
        have hw : |(2179901497/5000000000 : ℝ)|=(2179901497/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4359801011/10000000000 : ℝ)|^5335 ≤ (17897752841833/50000000000000 : ℝ)^4311
        have hw : |(4359801011/10000000000 : ℝ)|=(4359801011/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1714_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (5327/1024 : ℝ) ≤ p) (hpb : p ≤ (5335/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (196285051/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2133/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5021/50000 : ℝ)*pair X i i ≤ pair X i h) :
    -(2087/3125 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(1828/3125 : ℝ) ∧ (81611/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (1131/1250 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2133/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5021/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2133/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5021/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2133/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5021/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2133/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5021/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2133/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5021/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2133/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5021/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5021/50000 : ℝ) ^ (5327/1024 : ℝ) ≤ (641683100426309/100000000000000000000 : ℝ) := by
    have hpowers : (5021/50000 : ℝ)^5327 ≤ (641683100426309/100000000000000000000 : ℝ)^1024 := by
      have hnat : (5021 : ℕ)^5327*100000000000000000000^1024 ≤ 641683100426309^1024*50000^5327 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5021 50000 641683100426309 100000000000000000000 5327 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5021/50000 : ℝ)) (X := (641683100426309/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5327 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2133/12500 : ℝ) ^ (5327/1024 : ℝ) ≤ (10119767956856929/100000000000000000000 : ℝ) := by
    have hpowers : (2133/12500 : ℝ)^5327 ≤ (10119767956856929/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2133 : ℕ)^5327*100000000000000000000^1024 ≤ 10119767956856929^1024*12500^5327 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2133 12500 10119767956856929 100000000000000000000 5327 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2133/12500 : ℝ)) (X := (10119767956856929/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5327 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000641683100426309/50000000000000000000 : ℝ) ≤ (10000024669798723/10000000000000000 : ℝ) ^ (5327/1024 : ℝ) := by
    have hpowers : (50000641683100426309/50000000000000000000 : ℝ)^1024 ≤ (10000024669798723/10000000000000000 : ℝ)^5327 := by
      have hnat : (50000641683100426309 : ℕ)^1024*10000000000000000^5327 ≤ 10000024669798723^5327*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000641683100426309 50000000000000000000 10000024669798723 10000000000000000 1024 5327 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000024669798723/10000000000000000 : ℝ)) (X := (50000641683100426309/50000000000000000000 : ℝ)) (by norm_num) 5327 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50005380725528641619/50000000000000000000 : ℝ) ≤ (5000103428261241/5000000000000000 : ℝ) ^ (5327/1024 : ℝ) := by
    have hpowers : (50005380725528641619/50000000000000000000 : ℝ)^1024 ≤ (5000103428261241/5000000000000000 : ℝ)^5327 := by
      have hnat : (50005380725528641619 : ℕ)^1024*5000000000000000^5327 ≤ 5000103428261241^5327*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005380725528641619 50000000000000000000 5000103428261241 5000000000000000 1024 5327 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000103428261241/5000000000000000 : ℝ)) (X := (50005380725528641619/50000000000000000000 : ℝ)) (by norm_num) 5327 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50010119767956856929/50000000000000000000 : ℝ) ≤ (10000389043246241/10000000000000000 : ℝ) ^ (5327/1024 : ℝ) := by
    have hpowers : (50010119767956856929/50000000000000000000 : ℝ)^1024 ≤ (10000389043246241/10000000000000000 : ℝ)^5327 := by
      have hnat : (50010119767956856929 : ℕ)^1024*10000000000000000^5327 ≤ 10000389043246241^5327*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010119767956856929 50000000000000000000 10000389043246241 10000000000000000 1024 5327 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000389043246241/10000000000000000 : ℝ)) (X := (50010119767956856929/50000000000000000000 : ℝ)) (by norm_num) 5327 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(641683100426309/100000000000000000000 : ℝ) ≤ ((1404330283863333143/1404400000000000000 : ℝ)+2*(182186723759/702200000000000 : ℝ)*(5021/50000 : ℝ))^(5327/1024 : ℝ) := by
    rw [show (1404330283863333143/1404400000000000000 : ℝ)+2*(182186723759/702200000000000 : ℝ)*(5021/50000 : ℝ)=(10000024669798723/10000000000000000 : ℝ) by norm_num, show 1+2*(641683100426309/100000000000000000000 : ℝ)=(50000641683100426309/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(10119767956856929/100000000000000000000 : ℝ)+(641683100426309/100000000000000000000 : ℝ) ≤ ((1404330283863333143/1404400000000000000 : ℝ)+(182186723759/702200000000000 : ℝ)*((2133/12500 : ℝ)+(5021/50000 : ℝ)))^(5327/1024 : ℝ) := by
    rw [show (1404330283863333143/1404400000000000000 : ℝ)+(182186723759/702200000000000 : ℝ)*((2133/12500 : ℝ)+(5021/50000 : ℝ))=(5000103428261241/5000000000000000 : ℝ) by norm_num, show 1+(10119767956856929/100000000000000000000 : ℝ)+(641683100426309/100000000000000000000 : ℝ)=(50005380725528641619/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(10119767956856929/100000000000000000000 : ℝ) ≤ ((1404330283863333143/1404400000000000000 : ℝ)+2*(182186723759/702200000000000 : ℝ)*(2133/12500 : ℝ))^(5327/1024 : ℝ) := by
    rw [show (1404330283863333143/1404400000000000000 : ℝ)+2*(182186723759/702200000000000 : ℝ)*(2133/12500 : ℝ)=(10000389043246241/10000000000000000 : ℝ) by norm_num, show 1+2*(10119767956856929/100000000000000000000 : ℝ)=(50010119767956856929/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1404330283863333143/1404400000000000000 : ℝ)*(X 1 0+X 2 0)+(182186723759/702200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5327/1024 : ℝ)) (lo := (5021/50000 : ℝ)) (hi := (2133/12500 : ℝ)) (c := (1404330283863333143/1404400000000000000 : ℝ)) (alpha := (182186723759/702200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1404330283863333143/1404400000000000000 : ℝ)*(X 0 1+X 2 1)+(182186723759/702200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5327/1024 : ℝ)) (lo := (5021/50000 : ℝ)) (hi := (2133/12500 : ℝ)) (c := (1404330283863333143/1404400000000000000 : ℝ)) (alpha := (182186723759/702200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1404330283863333143/1404400000000000000 : ℝ)*(X 0 2+X 1 2)+(182186723759/702200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5327/1024 : ℝ)) (lo := (5021/50000 : ℝ)) (hi := (2133/12500 : ℝ)) (c := (1404330283863333143/1404400000000000000 : ℝ)) (alpha := (182186723759/702200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1082201391/10000000000 : ℝ)*X 0 0+(2707559889/5000000000 : ℝ)*X 0 1+(135378001/250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1714_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5225200153/10000000000 : ℝ)*X 1 0+(-1351909293/10000000000 : ℝ)*X 1 1+(5415119953/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1714_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2612599837/5000000000 : ℝ)*X 2 0+(5415120311/10000000000 : ℝ)*X 2 1+(-84494341/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1714_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((448104727/1000000000 : ℝ)*X 0 0+(1965166963/5000000000 : ℝ)*X 0 1+(1965166939/5000000000 : ℝ)*X 0 2+(448104727/1000000000 : ℝ)*X 1 0+(1965166963/5000000000 : ℝ)*X 1 1+(1965166939/5000000000 : ℝ)*X 1 2+(448104727/1000000000 : ℝ)*X 2 0+(1965166963/5000000000 : ℝ)*X 2 1+(1965166939/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1714_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1733881941/10000000000 : ℝ)*X 0 0+(5177637133/10000000000 : ℝ)*X 0 1+(2588818527/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1714_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2693051079/5000000000 : ℝ)*X 1 0+(-291357477/2000000000 : ℝ)*X 1 1+(2588818401/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1714_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5386101817/10000000000 : ℝ)*X 2 0+(2588818583/5000000000 : ℝ)*X 2 1+(-1456787359/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1714_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1851155283/5000000000 : ℝ)*X 0 0+(4318881401/10000000000 : ℝ)*X 0 1+(431888099/1000000000 : ℝ)*X 0 2+(1851155283/5000000000 : ℝ)*X 1 0+(4318881401/10000000000 : ℝ)*X 1 1+(431888099/1000000000 : ℝ)*X 1 2+(1851155283/5000000000 : ℝ)*X 2 0+(4318881401/10000000000 : ℝ)*X 2 1+(431888099/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1714_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-199207941/1250000000 : ℝ)*X 0 0+(625269849/1250000000 : ℝ)*X 0 1+(5457698347/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1714_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5196371453/10000000000 : ℝ)*X 1 0+(-666168439/5000000000 : ℝ)*X 1 1+(5457698931/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1714_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((1039274677/2000000000 : ℝ)*X 2 0+(5457697321/10000000000 : ℝ)*X 2 1+(-66616823/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1714_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4615693173/10000000000 : ℝ)*X 0 0+(1930243451/5000000000 : ℝ)*X 0 1+(6176779/16000000 : ℝ)*X 0 2+(4615693173/10000000000 : ℝ)*X 1 0+(1930243451/5000000000 : ℝ)*X 1 1+(6176779/16000000 : ℝ)*X 1 2+(4615693173/10000000000 : ℝ)*X 2 0+(1930243451/5000000000 : ℝ)*X 2 1+(6176779/16000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1714_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1216852731/10000000000 : ℝ)*X 0 0+(2791184793/5000000000 : ℝ)*X 0 1+(644069803/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1714_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5403125297/10000000000 : ℝ)*X 1 0+(-733710379/5000000000 : ℝ)*X 1 1+(2576278897/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1714_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((2701562543/5000000000 : ℝ)*X 2 0+(2576278847/5000000000 : ℝ)*X 2 1+(-1467421181/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1714_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((1808544659/5000000000 : ℝ)*X 0 0+(2179901497/5000000000 : ℝ)*X 0 1+(4359801011/10000000000 : ℝ)*X 0 2+(1808544659/5000000000 : ℝ)*X 1 0+(2179901497/5000000000 : ℝ)*X 1 1+(4359801011/10000000000 : ℝ)*X 1 2+(1808544659/5000000000 : ℝ)*X 2 0+(2179901497/5000000000 : ℝ)*X 2 1+(4359801011/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1714_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-2087/3125 : ℝ) ≤ (-375153844605340957122473769753/561760000000000000000000000000 : ℝ) := by norm_num
    linear_combination (20409453/100000000000000 : ℝ)*(upper1) + (20314357/100000000000000 : ℝ)*(upper2) + (20955541/50000000000000 : ℝ)*(upper3) + (1305383/20000000000000 : ℝ)*(upper5) + (10934151651323/800000000000 : ℝ)*(major0) + (10934151651323/800000000000 : ℝ)*(major1) + (10934151651323/800000000000 : ℝ)*(major2) + (1545383919/50000000000000 : ℝ)*(sp1) + (11626771/2500000000000 : ℝ)*(sp3) + (514870030412233/25000000000000 : ℝ)*(sp4) + (1029738515440547/50000000000000 : ℝ)*(sp5) + (257435001780323/12500000000000 : ℝ)*(sp6) + (696317950138159/100000000000000 : ℝ)*(sp7) + (26851587/25000000000000 : ℝ)*(sp14) + (696318415208999/100000000000000 : ℝ)*(f.failure) + (514870030412233/25000000000000 : ℝ)*(f.sum) + (26581490733721/7022000000000000000000000000 : ℝ)*base65 + (1709885680341411/1123520000000000000000000000000 : ℝ)*base68 + (3859348758175971/1123520000000000000000000000000 : ℝ)*base70 + (8443441304989/1123520000000000000000000000000 : ℝ)*base71 + (630874577013/280880000000000000000000000 : ℝ)*base74 + (8940093459748451/1123520000000000000000000000000 : ℝ)*base76 + (2484972524220189/1123520000000000000000000000000 : ℝ)*base77 + (1167367645621411/1123520000000000000000000000000 : ℝ)*base80 + (83758737893367/7022000000000000000000000000 : ℝ)*base82 + (44373949/10000000000000000000000 : ℝ)*base89 + (44373949/10000000000000000000000 : ℝ)*base91 + (44373949/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (1828/3125 : ℝ) ≤ (4107776181442765282414064688093/7022000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (48843333/100000000000000 : ℝ)*(lower0) + (5505957/25000000000000 : ℝ)*(upper2) + (33594521/50000000000000 : ℝ)*(lower4) + (147273979542217/10000000000000 : ℝ)*(major0) + (147273979542217/10000000000000 : ℝ)*(major1) + (147273979542217/10000000000000 : ℝ)*(major2) + (543917974224809/25000000000000 : ℝ)*(sp0) + (2175672536926587/100000000000000 : ℝ)*(sp1) + (217567160456649/10000000000000 : ℝ)*(sp2) + (93788319268041/12500000000000 : ℝ)*(sp3) + (169364181/20000000000000 : ℝ)*(sp5) + (889590501/50000000000000 : ℝ)*(sp6) + (4915393/5000000000000 : ℝ)*(sp7) + (1486848257/100000000000000 : ℝ)*(sp12) + (187576663113047/25000000000000 : ℝ)*(f.failure) + (543918345936873/25000000000000 : ℝ)*(f.sum) + (333070923379/54859375000000000000000000 : ℝ)*base65 + (121574522331907969/14044000000000000000000000000000 : ℝ)*base68 + (135631119715643969/14044000000000000000000000000000 : ℝ)*base70 + (138328947455880031/14044000000000000000000000000000 : ℝ)*base71 + (11090853432811/3511000000000000000000000000 : ℝ)*base73 + (57707702209415969/14044000000000000000000000000000 : ℝ)*base76 + (86348956293788031/14044000000000000000000000000000 : ℝ)*base77 + (19540614190435969/14044000000000000000000000000000 : ℝ)*base80 + (5190213978217/3511000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (839603/2500000000000000000000 : ℝ)*base90 + (839603/2500000000000000000000 : ℝ)*base92 + (839603/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (81611/100000 : ℝ) ≤ (5730866386200270042342280200879/7022000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (28375201/50000000000000 : ℝ)*(upper0) + (17155199/50000000000000 : ℝ)*(lower1) + (45774327/50000000000000 : ℝ)*(lower3) + (143638927/50000000000000 : ℝ)*(upper4) + (149101354826051/10000000000000 : ℝ)*(major0) + (149101354826051/10000000000000 : ℝ)*(major1) + (149101354826051/10000000000000 : ℝ)*(major2) + (782730553/20000000000000 : ℝ)*(sp0) + (23732600483/50000000000000 : ℝ)*(sp1) + (31486532273/100000000000000 : ℝ)*(sp3) + (2195202386189941/100000000000000 : ℝ)*(sp8) + (109757941732087/5000000000000 : ℝ)*(sp9) + (2195206299842707/100000000000000 : ℝ)*(sp10) + (379792484783923/50000000000000 : ℝ)*(sp11) + (379808228050059/50000000000000 : ℝ)*(f.failure) + (2195206299842707/100000000000000 : ℝ)*(f.sum) + (8804448667473/1755500000000000000000000000 : ℝ)*base66 + (21473572679081707/14044000000000000000000000000000 : ℝ)*base68 + (44514131146402293/14044000000000000000000000000000 : ℝ)*base69 + (134459122152257707/14044000000000000000000000000000 : ℝ)*base72 + (12686854480257/3511000000000000000000000000 : ℝ)*base73 + (39868145470318293/14044000000000000000000000000000 : ℝ)*base75 + (98000296746045707/14044000000000000000000000000000 : ℝ)*base78 + (21252948531301707/14044000000000000000000000000000 : ℝ)*base80 + (4057643311149/702200000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (38631991/5000000000000000000000 : ℝ)*base90 + (38631991/5000000000000000000000 : ℝ)*base92 + (38631991/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (-1131/1250 : ℝ) ≤ (-15883275833740799471114448529461/17555000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (120966259/100000000000000 : ℝ)*(upper1) + (126241399/100000000000000 : ℝ)*(upper3) + (30029507/50000000000000 : ℝ)*(lower4) + (385171673789409/25000000000000 : ℝ)*(major0) + (385171673789409/25000000000000 : ℝ)*(major1) + (385171673789409/25000000000000 : ℝ)*(major2) + (3135022857/50000000000000 : ℝ)*(sp4) + (66819208207/100000000000000 : ℝ)*(sp5) + (73261382909/100000000000000 : ℝ)*(sp6) + (14864214379/50000000000000 : ℝ)*(sp7) + (1163301549724889/50000000000000 : ℝ)*(sp12) + (465308510057457/20000000000000 : ℝ)*(sp13) + (1163268054056291/50000000000000 : ℝ)*(sp14) + (196223341365931/25000000000000 : ℝ)*(sp15) + (392461546946241/50000000000000 : ℝ)*(f.failure) + (581652342373873/25000000000000 : ℝ)*(f.sum) + (26390820800061/8777500000000000000000000000 : ℝ)*base65 + (25592662345704487/35110000000000000000000000000000 : ℝ)*base67 + (221482809190375513/35110000000000000000000000000000 : ℝ)*base70 + (104216341716734487/35110000000000000000000000000000 : ℝ)*base71 + (11152373209533/17555000000000000000000000000 : ℝ)*base74 + (146009190206735513/35110000000000000000000000000000 : ℝ)*base76 + (166040896307794487/35110000000000000000000000000000 : ℝ)*base77 + (238276686013184487/35110000000000000000000000000000 : ℝ)*base79 + (42030502415257/17555000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (8943291/5000000000000000000000 : ℝ)*base89 + (8943291/5000000000000000000000 : ℝ)*base91 + (8943291/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1714_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (5327/1024 : ℝ) ≤ p) (hpb : p ≤ (5335/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (196285051/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2133/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5021/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(2087/3125 : ℝ) ≤ X j i ∧ X j i ≤ -(1828/3125 : ℝ) else (81611/100000 : ℝ) ≤ X j i ∧ X j i ≤ (1131/1250 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1714_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1714_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5327/1024 : ℝ) ≤ p) (hpb : p ≤ (5335/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (196285051/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8537/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10033/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(2087/3125 : ℝ) ≤ X j i ∧ X j i ≤ -(1828/3125 : ℝ) else (81611/100000 : ℝ) ≤ X j i ∧ X j i ≤ (1131/1250 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1714_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1714_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5327/1024 : ℝ) ≤ p) (hpb : p ≤ (5335/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (196285051/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8537/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10033/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(2087/3125 : ℝ) ≤ X j i ∧ X j i ≤ -(1828/3125 : ℝ) else (81611/100000 : ℝ) ≤ X j i ∧ X j i ≤ (1131/1250 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1714_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
