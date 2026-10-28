-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1294_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:27:03.410237+00:00
-- url     : https://prove2.me/submissions/c62c394b-5467-4cc8-836f-1af6343c8c65

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
theorem support_rectangle_w1294_s3_0 (p : ℝ) (hpa : (4253/1024 : ℝ) ≤ p) (hpb : p ≤ (2127/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-32560179/156250000 : ℝ)*x 0 + (2716890021/5000000000 : ℝ)*x 1 + (326621077/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (32560179/156250000 : ℝ)^2127 ≤ (12674433030597/100000000000000 : ℝ)^1615 := by
    have hnat : (32560179 : ℕ)^2127*100000000000000^1615 ≤ 12674433030597^1615*156250000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      32560179 156250000 12674433030597 100000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2716890021/5000000000 : ℝ)^2127 ≤ (44783911662931/100000000000000 : ℝ)^1615 := by
    have hnat : (2716890021 : ℕ)^2127*100000000000000^1615 ≤ 44783911662931^1615*5000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2716890021 5000000000 44783911662931 100000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (326621077/625000000 : ℝ)^2127 ≤ (42541655279757/100000000000000 : ℝ)^1615 := by
    have hnat : (326621077 : ℕ)^2127*100000000000000^1615 ≤ 42541655279757^1615*625000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      326621077 625000000 42541655279757 100000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2127/512 : ℝ)) 2127 1615 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-32560179/156250000 : ℝ), (2716890021/5000000000 : ℝ), (326621077/625000000 : ℝ)] ![(12674433030597/100000000000000 : ℝ), (44783911662931/100000000000000 : ℝ), (42541655279757/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-32560179/156250000 : ℝ)|^2127 ≤ (12674433030597/100000000000000 : ℝ)^1615
        have hw : |(-32560179/156250000 : ℝ)|=(32560179/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2716890021/5000000000 : ℝ)|^2127 ≤ (44783911662931/100000000000000 : ℝ)^1615
        have hw : |(2716890021/5000000000 : ℝ)|=(2716890021/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(326621077/625000000 : ℝ)|^2127 ≤ (42541655279757/100000000000000 : ℝ)^1615
        have hw : |(326621077/625000000 : ℝ)|=(326621077/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1294_s3_1 (p : ℝ) (hpa : (4253/1024 : ℝ) ≤ p) (hpb : p ≤ (2127/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5354473423/10000000000 : ℝ)*x 0 + (-2190216227/10000000000 : ℝ)*x 1 + (5225937321/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5354473423/10000000000 : ℝ)^2127 ≤ (43925066082299/100000000000000 : ℝ)^1615 := by
    have hnat : (5354473423 : ℕ)^2127*100000000000000^1615 ≤ 43925066082299^1615*10000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5354473423 10000000000 43925066082299 100000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2190216227/10000000000 : ℝ)^2127 ≤ (6766638830491/50000000000000 : ℝ)^1615 := by
    have hnat : (2190216227 : ℕ)^2127*50000000000000^1615 ≤ 6766638830491^1615*10000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2190216227 10000000000 6766638830491 50000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5225937321/10000000000 : ℝ)^2127 ≤ (10635414058487/25000000000000 : ℝ)^1615 := by
    have hnat : (5225937321 : ℕ)^2127*25000000000000^1615 ≤ 10635414058487^1615*10000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5225937321 10000000000 10635414058487 25000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2127/512 : ℝ)) 2127 1615 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5354473423/10000000000 : ℝ), (-2190216227/10000000000 : ℝ), (5225937321/10000000000 : ℝ)] ![(43925066082299/100000000000000 : ℝ), (6766638830491/50000000000000 : ℝ), (10635414058487/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5354473423/10000000000 : ℝ)|^2127 ≤ (43925066082299/100000000000000 : ℝ)^1615
        have hw : |(5354473423/10000000000 : ℝ)|=(5354473423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2190216227/10000000000 : ℝ)|^2127 ≤ (6766638830491/50000000000000 : ℝ)^1615
        have hw : |(-2190216227/10000000000 : ℝ)|=(2190216227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5225937321/10000000000 : ℝ)|^2127 ≤ (10635414058487/25000000000000 : ℝ)^1615
        have hw : |(5225937321/10000000000 : ℝ)|=(5225937321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1294_s3_2 (p : ℝ) (hpa : (4253/1024 : ℝ) ≤ p) (hpb : p ≤ (2127/512 : ℝ)) (x : Fin 3 → ℝ) :
    (214178939/400000000 : ℝ)*x 0 + (2612968523/5000000000 : ℝ)*x 1 + (-2190216521/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (214178939/400000000 : ℝ)^2127 ≤ (8785013328823/20000000000000 : ℝ)^1615 := by
    have hnat : (214178939 : ℕ)^2127*20000000000000^1615 ≤ 8785013328823^1615*400000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      214178939 400000000 8785013328823 20000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2612968523/5000000000 : ℝ)^2127 ≤ (21270826642803/50000000000000 : ℝ)^1615 := by
    have hnat : (2612968523 : ℕ)^2127*50000000000000^1615 ≤ 21270826642803^1615*5000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2612968523 5000000000 21270826642803 50000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2190216521/10000000000 : ℝ)^2127 ≤ (13533280053517/100000000000000 : ℝ)^1615 := by
    have hnat : (2190216521 : ℕ)^2127*100000000000000^1615 ≤ 13533280053517^1615*10000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2190216521 10000000000 13533280053517 100000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2127/512 : ℝ)) 2127 1615 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(214178939/400000000 : ℝ), (2612968523/5000000000 : ℝ), (-2190216521/10000000000 : ℝ)] ![(8785013328823/20000000000000 : ℝ), (21270826642803/50000000000000 : ℝ), (13533280053517/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(214178939/400000000 : ℝ)|^2127 ≤ (8785013328823/20000000000000 : ℝ)^1615
        have hw : |(214178939/400000000 : ℝ)|=(214178939/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2612968523/5000000000 : ℝ)|^2127 ≤ (21270826642803/50000000000000 : ℝ)^1615
        have hw : |(2612968523/5000000000 : ℝ)|=(2612968523/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2190216521/10000000000 : ℝ)|^2127 ≤ (13533280053517/100000000000000 : ℝ)^1615
        have hw : |(-2190216521/10000000000 : ℝ)|=(2190216521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1294_s3_3 (p : ℝ) (hpa : (4253/1024 : ℝ) ≤ p) (hpb : p ≤ (2127/512 : ℝ)) (x : Fin 3 → ℝ) :
    (433792733/1000000000 : ℝ)*x 0 + (4129206119/10000000000 : ℝ)*x 1 + (182267969/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (433792733/1000000000 : ℝ)^2127 ≤ (33288225591929/100000000000000 : ℝ)^1615 := by
    have hnat : (433792733 : ℕ)^2127*100000000000000^1615 ≤ 33288225591929^1615*1000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      433792733 1000000000 33288225591929 100000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4129206119/10000000000 : ℝ)^2127 ≤ (6239008175579/20000000000000 : ℝ)^1615 := by
    have hnat : (4129206119 : ℕ)^2127*20000000000000^1615 ≤ 6239008175579^1615*10000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4129206119 10000000000 6239008175579 20000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (182267969/400000000 : ℝ)^2127 ≤ (7103346702761/20000000000000 : ℝ)^1615 := by
    have hnat : (182267969 : ℕ)^2127*20000000000000^1615 ≤ 7103346702761^1615*400000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      182267969 400000000 7103346702761 20000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2127/512 : ℝ)) 2127 1615 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(433792733/1000000000 : ℝ), (4129206119/10000000000 : ℝ), (182267969/400000000 : ℝ)] ![(33288225591929/100000000000000 : ℝ), (6239008175579/20000000000000 : ℝ), (7103346702761/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(433792733/1000000000 : ℝ)|^2127 ≤ (33288225591929/100000000000000 : ℝ)^1615
        have hw : |(433792733/1000000000 : ℝ)|=(433792733/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4129206119/10000000000 : ℝ)|^2127 ≤ (6239008175579/20000000000000 : ℝ)^1615
        have hw : |(4129206119/10000000000 : ℝ)|=(4129206119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(182267969/400000000 : ℝ)|^2127 ≤ (7103346702761/20000000000000 : ℝ)^1615
        have hw : |(182267969/400000000 : ℝ)|=(182267969/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1294_s3_4 (p : ℝ) (hpa : (4253/1024 : ℝ) ≤ p) (hpb : p ≤ (2127/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-416774777/2000000000 : ℝ)*x 0 + (5226830937/10000000000 : ℝ)*x 1 + (5432880721/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (416774777/2000000000 : ℝ)^2127 ≤ (12674612697217/100000000000000 : ℝ)^1615 := by
    have hnat : (416774777 : ℕ)^2127*100000000000000^1615 ≤ 12674612697217^1615*2000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      416774777 2000000000 12674612697217 100000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5226830937/10000000000 : ℝ)^2127 ≤ (42551237168373/100000000000000 : ℝ)^1615 := by
    have hnat : (5226830937 : ℕ)^2127*100000000000000^1615 ≤ 42551237168373^1615*10000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5226830937 10000000000 42551237168373 100000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5432880721/10000000000 : ℝ)^2127 ≤ (22387075062189/50000000000000 : ℝ)^1615 := by
    have hnat : (5432880721 : ℕ)^2127*50000000000000^1615 ≤ 22387075062189^1615*10000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5432880721 10000000000 22387075062189 50000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2127/512 : ℝ)) 2127 1615 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-416774777/2000000000 : ℝ), (5226830937/10000000000 : ℝ), (5432880721/10000000000 : ℝ)] ![(12674612697217/100000000000000 : ℝ), (42551237168373/100000000000000 : ℝ), (22387075062189/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-416774777/2000000000 : ℝ)|^2127 ≤ (12674612697217/100000000000000 : ℝ)^1615
        have hw : |(-416774777/2000000000 : ℝ)|=(416774777/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5226830937/10000000000 : ℝ)|^2127 ≤ (42551237168373/100000000000000 : ℝ)^1615
        have hw : |(5226830937/10000000000 : ℝ)|=(5226830937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5432880721/10000000000 : ℝ)|^2127 ≤ (22387075062189/50000000000000 : ℝ)^1615
        have hw : |(5432880721/10000000000 : ℝ)|=(5432880721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1294_s3_5 (p : ℝ) (hpa : (4253/1024 : ℝ) ≤ p) (hpb : p ≤ (2127/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1060248597/2000000000 : ℝ)*x 0 + (-198327271/1000000000 : ℝ)*x 1 + (5432880677/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1060248597/2000000000 : ℝ)^2127 ≤ (43350864764121/100000000000000 : ℝ)^1615 := by
    have hnat : (1060248597 : ℕ)^2127*100000000000000^1615 ≤ 43350864764121^1615*2000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1060248597 2000000000 43350864764121 100000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (198327271/1000000000 : ℝ)^2127 ≤ (11874985571733/100000000000000 : ℝ)^1615 := by
    have hnat : (198327271 : ℕ)^2127*100000000000000^1615 ≤ 11874985571733^1615*1000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      198327271 1000000000 11874985571733 100000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5432880677/10000000000 : ℝ)^2127 ≤ (111935374117/250000000000 : ℝ)^1615 := by
    have hnat : (5432880677 : ℕ)^2127*250000000000^1615 ≤ 111935374117^1615*10000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5432880677 10000000000 111935374117 250000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2127/512 : ℝ)) 2127 1615 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1060248597/2000000000 : ℝ), (-198327271/1000000000 : ℝ), (5432880677/10000000000 : ℝ)] ![(43350864764121/100000000000000 : ℝ), (11874985571733/100000000000000 : ℝ), (111935374117/250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1060248597/2000000000 : ℝ)|^2127 ≤ (43350864764121/100000000000000 : ℝ)^1615
        have hw : |(1060248597/2000000000 : ℝ)|=(1060248597/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-198327271/1000000000 : ℝ)|^2127 ≤ (11874985571733/100000000000000 : ℝ)^1615
        have hw : |(-198327271/1000000000 : ℝ)|=(198327271/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5432880677/10000000000 : ℝ)|^2127 ≤ (111935374117/250000000000 : ℝ)^1615
        have hw : |(5432880677/10000000000 : ℝ)|=(5432880677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1294_s3_6 (p : ℝ) (hpa : (4253/1024 : ℝ) ≤ p) (hpb : p ≤ (2127/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5301243033/10000000000 : ℝ)*x 0 + (5432880609/10000000000 : ℝ)*x 1 + (-1983272739/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5301243033/10000000000 : ℝ)^2127 ≤ (1083771632027/2500000000000 : ℝ)^1615 := by
    have hnat : (5301243033 : ℕ)^2127*2500000000000^1615 ≤ 1083771632027^1615*10000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5301243033 10000000000 1083771632027 2500000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5432880609/10000000000 : ℝ)^2127 ≤ (11193537227181/25000000000000 : ℝ)^1615 := by
    have hnat : (5432880609 : ℕ)^2127*25000000000000^1615 ≤ 11193537227181^1615*10000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5432880609 10000000000 11193537227181 25000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1983272739/10000000000 : ℝ)^2127 ≤ (11874985800421/100000000000000 : ℝ)^1615 := by
    have hnat : (1983272739 : ℕ)^2127*100000000000000^1615 ≤ 11874985800421^1615*10000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1983272739 10000000000 11874985800421 100000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2127/512 : ℝ)) 2127 1615 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5301243033/10000000000 : ℝ), (5432880609/10000000000 : ℝ), (-1983272739/10000000000 : ℝ)] ![(1083771632027/2500000000000 : ℝ), (11193537227181/25000000000000 : ℝ), (11874985800421/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5301243033/10000000000 : ℝ)|^2127 ≤ (1083771632027/2500000000000 : ℝ)^1615
        have hw : |(5301243033/10000000000 : ℝ)|=(5301243033/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5432880609/10000000000 : ℝ)|^2127 ≤ (11193537227181/25000000000000 : ℝ)^1615
        have hw : |(5432880609/10000000000 : ℝ)|=(5432880609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1983272739/10000000000 : ℝ)|^2127 ≤ (11874985800421/100000000000000 : ℝ)^1615
        have hw : |(-1983272739/10000000000 : ℝ)|=(1983272739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1294_s3_7 (p : ℝ) (hpa : (4253/1024 : ℝ) ≤ p) (hpb : p ≤ (2127/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2168986577/5000000000 : ℝ)*x 0 + (455486081/1000000000 : ℝ)*x 1 + (2065528029/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2168986577/5000000000 : ℝ)^2127 ≤ (33288688715687/100000000000000 : ℝ)^1615 := by
    have hnat : (2168986577 : ℕ)^2127*100000000000000^1615 ≤ 33288688715687^1615*5000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2168986577 5000000000 33288688715687 100000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (455486081/1000000000 : ℝ)^2127 ≤ (887446564497/2500000000000 : ℝ)^1615 := by
    have hnat : (455486081 : ℕ)^2127*2500000000000^1615 ≤ 887446564497^1615*1000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      455486081 1000000000 887446564497 2500000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2065528029/5000000000 : ℝ)^2127 ≤ (7803362172853/25000000000000 : ℝ)^1615 := by
    have hnat : (2065528029 : ℕ)^2127*25000000000000^1615 ≤ 7803362172853^1615*5000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2065528029 5000000000 7803362172853 25000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2127/512 : ℝ)) 2127 1615 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2168986577/5000000000 : ℝ), (455486081/1000000000 : ℝ), (2065528029/5000000000 : ℝ)] ![(33288688715687/100000000000000 : ℝ), (887446564497/2500000000000 : ℝ), (7803362172853/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2168986577/5000000000 : ℝ)|^2127 ≤ (33288688715687/100000000000000 : ℝ)^1615
        have hw : |(2168986577/5000000000 : ℝ)|=(2168986577/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(455486081/1000000000 : ℝ)|^2127 ≤ (887446564497/2500000000000 : ℝ)^1615
        have hw : |(455486081/1000000000 : ℝ)|=(455486081/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2065528029/5000000000 : ℝ)|^2127 ≤ (7803362172853/25000000000000 : ℝ)^1615
        have hw : |(2065528029/5000000000 : ℝ)|=(2065528029/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1294_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4253/1024 : ℝ) ≤ p) (hpb : p ≤ (2127/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152840397/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4077/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9519/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10667/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1883/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4077/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9519/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4077/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9519/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4077/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9519/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4077/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9519/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4077/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9519/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4077/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9519/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9519/100000 : ℝ) ^ (4253/1024 : ℝ) ≤ (2862415102676363/50000000000000000000 : ℝ) := by
    have hpowers : (9519/100000 : ℝ)^4253 ≤ (2862415102676363/50000000000000000000 : ℝ)^1024 := by
      have hnat : (9519 : ℕ)^4253*50000000000000000000^1024 ≤ 2862415102676363^1024*100000^4253 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9519 100000 2862415102676363 50000000000000000000 4253 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9519/100000 : ℝ)) (X := (2862415102676363/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4253 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (4077/25000 : ℝ) ^ (4253/1024 : ℝ) ≤ (2678044844378801/5000000000000000000 : ℝ) := by
    have hpowers : (4077/25000 : ℝ)^4253 ≤ (2678044844378801/5000000000000000000 : ℝ)^1024 := by
      have hnat : (4077 : ℕ)^4253*5000000000000000000^1024 ≤ 2678044844378801^1024*25000^4253 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4077 25000 2678044844378801 5000000000000000000 4253 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4077/25000 : ℝ)) (X := (2678044844378801/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4253 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25002862415102676363/25000000000000000000 : ℝ) ≤ (5000137831444823/5000000000000000 : ℝ) ^ (4253/1024 : ℝ) := by
    have hpowers : (25002862415102676363/25000000000000000000 : ℝ)^1024 ≤ (5000137831444823/5000000000000000 : ℝ)^4253 := by
      have hnat : (25002862415102676363 : ℕ)^1024*5000000000000000^4253 ≤ 5000137831444823^4253*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25002862415102676363 25000000000000000000 5000137831444823 5000000000000000 1024 4253 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000137831444823/5000000000000000 : ℝ)) (X := (25002862415102676363/25000000000000000000 : ℝ)) (by norm_num) 4253 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50029642863546464373/50000000000000000000 : ℝ) ≤ (400057084341773/400000000000000 : ℝ) ^ (4253/1024 : ℝ) := by
    have hpowers : (50029642863546464373/50000000000000000000 : ℝ)^1024 ≤ (400057084341773/400000000000000 : ℝ)^4253 := by
      have hnat : (50029642863546464373 : ℕ)^1024*400000000000000^4253 ≤ 400057084341773^4253*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50029642863546464373 50000000000000000000 400057084341773 400000000000000 1024 4253 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400057084341773/400000000000000 : ℝ)) (X := (50029642863546464373/50000000000000000000 : ℝ)) (by norm_num) 4253 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (2502678044844378801/2500000000000000000 : ℝ) ≤ (2500644638549751/2500000000000000 : ℝ) ^ (4253/1024 : ℝ) := by
    have hpowers : (2502678044844378801/2500000000000000000 : ℝ)^1024 ≤ (2500644638549751/2500000000000000 : ℝ)^4253 := by
      have hnat : (2502678044844378801 : ℕ)^1024*2500000000000000^4253 ≤ 2500644638549751^4253*2500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2502678044844378801 2500000000000000000 2500644638549751 2500000000000000 1024 4253 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500644638549751/2500000000000000 : ℝ)) (X := (2502678044844378801/2500000000000000000 : ℝ)) (by norm_num) 4253 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2862415102676363/50000000000000000000 : ℝ) ≤ ((5655829187748668991/5657500000000000000 : ℝ)+2*(1151445654679/678900000000000 : ℝ)*(9519/100000 : ℝ))^(4253/1024 : ℝ) := by
    rw [show (5655829187748668991/5657500000000000000 : ℝ)+2*(1151445654679/678900000000000 : ℝ)*(9519/100000 : ℝ)=(5000137831444823/5000000000000000 : ℝ) by norm_num, show 1+2*(2862415102676363/50000000000000000000 : ℝ)=(25002862415102676363/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2678044844378801/5000000000000000000 : ℝ)+(2862415102676363/50000000000000000000 : ℝ) ≤ ((5655829187748668991/5657500000000000000 : ℝ)+(1151445654679/678900000000000 : ℝ)*((4077/25000 : ℝ)+(9519/100000 : ℝ)))^(4253/1024 : ℝ) := by
    rw [show (5655829187748668991/5657500000000000000 : ℝ)+(1151445654679/678900000000000 : ℝ)*((4077/25000 : ℝ)+(9519/100000 : ℝ))=(400057084341773/400000000000000 : ℝ) by norm_num, show 1+(2678044844378801/5000000000000000000 : ℝ)+(2862415102676363/50000000000000000000 : ℝ)=(50029642863546464373/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2678044844378801/5000000000000000000 : ℝ) ≤ ((5655829187748668991/5657500000000000000 : ℝ)+2*(1151445654679/678900000000000 : ℝ)*(4077/25000 : ℝ))^(4253/1024 : ℝ) := by
    rw [show (5655829187748668991/5657500000000000000 : ℝ)+2*(1151445654679/678900000000000 : ℝ)*(4077/25000 : ℝ)=(2500644638549751/2500000000000000 : ℝ) by norm_num, show 1+2*(2678044844378801/5000000000000000000 : ℝ)=(2502678044844378801/2500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5655829187748668991/5657500000000000000 : ℝ)*(X 1 0+X 2 0)+(1151445654679/678900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4253/1024 : ℝ)) (lo := (9519/100000 : ℝ)) (hi := (4077/25000 : ℝ)) (c := (5655829187748668991/5657500000000000000 : ℝ)) (alpha := (1151445654679/678900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5655829187748668991/5657500000000000000 : ℝ)*(X 0 1+X 2 1)+(1151445654679/678900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4253/1024 : ℝ)) (lo := (9519/100000 : ℝ)) (hi := (4077/25000 : ℝ)) (c := (5655829187748668991/5657500000000000000 : ℝ)) (alpha := (1151445654679/678900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5655829187748668991/5657500000000000000 : ℝ)*(X 0 2+X 1 2)+(1151445654679/678900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4253/1024 : ℝ)) (lo := (9519/100000 : ℝ)) (hi := (4077/25000 : ℝ)) (c := (5655829187748668991/5657500000000000000 : ℝ)) (alpha := (1151445654679/678900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-32560179/156250000 : ℝ)*X 0 0+(2716890021/5000000000 : ℝ)*X 0 1+(326621077/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1294_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5354473423/10000000000 : ℝ)*X 1 0+(-2190216227/10000000000 : ℝ)*X 1 1+(5225937321/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1294_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((214178939/400000000 : ℝ)*X 2 0+(2612968523/5000000000 : ℝ)*X 2 1+(-2190216521/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1294_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((433792733/1000000000 : ℝ)*X 0 0+(4129206119/10000000000 : ℝ)*X 0 1+(182267969/400000000 : ℝ)*X 0 2+(433792733/1000000000 : ℝ)*X 1 0+(4129206119/10000000000 : ℝ)*X 1 1+(182267969/400000000 : ℝ)*X 1 2+(433792733/1000000000 : ℝ)*X 2 0+(4129206119/10000000000 : ℝ)*X 2 1+(182267969/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1294_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-416774777/2000000000 : ℝ)*X 0 0+(5226830937/10000000000 : ℝ)*X 0 1+(5432880721/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1294_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1060248597/2000000000 : ℝ)*X 1 0+(-198327271/1000000000 : ℝ)*X 1 1+(5432880677/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1294_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5301243033/10000000000 : ℝ)*X 2 0+(5432880609/10000000000 : ℝ)*X 2 1+(-1983272739/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1294_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2168986577/5000000000 : ℝ)*X 0 0+(455486081/1000000000 : ℝ)*X 0 1+(2065528029/5000000000 : ℝ)*X 0 2+(2168986577/5000000000 : ℝ)*X 1 0+(455486081/1000000000 : ℝ)*X 1 1+(2065528029/5000000000 : ℝ)*X 1 2+(2168986577/5000000000 : ℝ)*X 2 0+(455486081/1000000000 : ℝ)*X 2 1+(2065528029/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1294_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (947129766748835341394643027/282875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (619403351/100000000000000 : ℝ)*(base19) + (196806043/25000000000000 : ℝ)*(base23) + (7239543/100000000000000 : ℝ)*(lower2) + (97418363/50000000000000 : ℝ)*(upper3) + (14415949/20000000000000 : ℝ)*(lower4) + (3575290123820737/100000000000000 : ℝ)*(major0) + (3575290123820737/100000000000000 : ℝ)*(major1) + (1787645061910369/50000000000000 : ℝ)*(major2) + (4811342076934963/100000000000000 : ℝ)*(sp0) + (300709275064811/6250000000000 : ℝ)*(sp1) + (962269646643231/20000000000000 : ℝ)*(sp2) + (584805994372669/25000000000000 : ℝ)*(sp3) + (1735876341/25000000000000 : ℝ)*(sp4) + (7138102891/100000000000000 : ℝ)*(sp7) + (73100972362299/3125000000000 : ℝ)*(f.failure) + (4811349020440327/100000000000000 : ℝ)*(f.sum) + (28269548258241/4526000000000000000000000000 : ℝ)*base66 + (8030970689231450899/1697250000000000000000000000000000 : ℝ)*base68 + (4198414840157540537/848625000000000000000000000000000 : ℝ)*base69 + (13919493808977950899/1697250000000000000000000000000000 : ℝ)*base72 + (15725205834783/4526000000000000000000000000 : ℝ)*base73 + (5760350365282040537/848625000000000000000000000000000 : ℝ)*base75 + (17778463646858175899/1697250000000000000000000000000000 : ℝ)*base78 + (2330597862145574101/1697250000000000000000000000000000 : ℝ)*base79 + (1998089475793/2121562500000000000000000000 : ℝ)*base81 + (3867703/312500000000000000000 : ℝ)*base89 + (3867703/312500000000000000000 : ℝ)*base91 + (742703/312500000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1838909754498457691037337/176796875000000000000000000000 : ℝ) := by norm_num
    linear_combination (1178748447/50000000000000 : ℝ)*(base19) + (2516849921/100000000000000 : ℝ)*(base23) + (49045913/20000000000000 : ℝ)*(upper3) + (11214539/20000000000000 : ℝ)*(lower4) + (51971791/20000000000000 : ℝ)*(upper5) + (9015966099563/250000000000 : ℝ)*(major0) + (9015966099563/250000000000 : ℝ)*(major1) + (9015966099563/250000000000 : ℝ)*(major2) + (4893327763/12500000000000 : ℝ)*(sp1) + (20053193667/50000000000000 : ℝ)*(sp2) + (2426597902068403/50000000000000 : ℝ)*(sp4) + (303322143751113/6250000000000 : ℝ)*(sp5) + (97063063617991/2000000000000 : ℝ)*(sp6) + (294947091100627/12500000000000 : ℝ)*(sp7) + (294947091100627/12500000000000 : ℝ)*(f.failure) + (2426597902068403/50000000000000 : ℝ)*(f.sum) + (18080661147827/3394500000000000000000000000 : ℝ)*base65 + (29709908223820951/4243125000000000000000000000000 : ℝ)*base68 + (43623173959450951/4243125000000000000000000000000 : ℝ)*base70 + (42214266715387201/4243125000000000000000000000000 : ℝ)*base72 + (7020305748869/848625000000000000000000000 : ℝ)*base73 + (38753433908317201/4243125000000000000000000000000 : ℝ)*base76 + (378723028867799/4243125000000000000000000000000 : ℝ)*base77 + (4957358880438451/4243125000000000000000000000000 : ℝ)*base80 + (1426119630379/424312500000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (2371081/1250000000000000000000 : ℝ)*base90 + (2371081/1250000000000000000000 : ℝ)*base92 + (2371081/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1294_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4253/1024 : ℝ) ≤ p) (hpb : p ≤ (2127/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152840397/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4077/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9519/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10667/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1883/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1294_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1294_s4_0 (p : ℝ) (hpa : (4253/1024 : ℝ) ≤ p) (hpb : p ≤ (2127/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-65179627/312500000 : ℝ)*x 0 + (541877873/1000000000 : ℝ)*x 1 + (5239695523/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (65179627/312500000 : ℝ)^2127 ≤ (12689627899697/100000000000000 : ℝ)^1615 := by
    have hnat : (65179627 : ℕ)^2127*100000000000000^1615 ≤ 12689627899697^1615*312500000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      65179627 312500000 12689627899697 100000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (541877873/1000000000 : ℝ)^2127 ≤ (8924229861887/20000000000000 : ℝ)^1615 := by
    have hnat : (541877873 : ℕ)^2127*20000000000000^1615 ≤ 8924229861887^1615*1000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      541877873 1000000000 8924229861887 20000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5239695523/10000000000 : ℝ)^2127 ≤ (4268922278731/10000000000000 : ℝ)^1615 := by
    have hnat : (5239695523 : ℕ)^2127*10000000000000^1615 ≤ 4268922278731^1615*10000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5239695523 10000000000 4268922278731 10000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2127/512 : ℝ)) 2127 1615 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-65179627/312500000 : ℝ), (541877873/1000000000 : ℝ), (5239695523/10000000000 : ℝ)] ![(12689627899697/100000000000000 : ℝ), (8924229861887/20000000000000 : ℝ), (4268922278731/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-65179627/312500000 : ℝ)|^2127 ≤ (12689627899697/100000000000000 : ℝ)^1615
        have hw : |(-65179627/312500000 : ℝ)|=(65179627/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(541877873/1000000000 : ℝ)|^2127 ≤ (8924229861887/20000000000000 : ℝ)^1615
        have hw : |(541877873/1000000000 : ℝ)|=(541877873/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5239695523/10000000000 : ℝ)|^2127 ≤ (4268922278731/10000000000000 : ℝ)^1615
        have hw : |(5239695523/10000000000 : ℝ)|=(5239695523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1294_s4_1 (p : ℝ) (hpa : (4253/1024 : ℝ) ≤ p) (hpb : p ≤ (2127/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5350681529/10000000000 : ℝ)*x 0 + (-2177103871/10000000000 : ℝ)*x 1 + (5239695741/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5350681529/10000000000 : ℝ)^2127 ≤ (43884102489021/100000000000000 : ℝ)^1615 := by
    have hnat : (5350681529 : ℕ)^2127*100000000000000^1615 ≤ 43884102489021^1615*10000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5350681529 10000000000 43884102489021 100000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2177103871/10000000000 : ℝ)^2127 ≤ (1678334045173/12500000000000 : ℝ)^1615 := by
    have hnat : (2177103871 : ℕ)^2127*12500000000000^1615 ≤ 1678334045173^1615*10000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2177103871 10000000000 1678334045173 12500000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5239695741/10000000000 : ℝ)^2127 ≤ (4268922512649/10000000000000 : ℝ)^1615 := by
    have hnat : (5239695741 : ℕ)^2127*10000000000000^1615 ≤ 4268922512649^1615*10000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5239695741 10000000000 4268922512649 10000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2127/512 : ℝ)) 2127 1615 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5350681529/10000000000 : ℝ), (-2177103871/10000000000 : ℝ), (5239695741/10000000000 : ℝ)] ![(43884102489021/100000000000000 : ℝ), (1678334045173/12500000000000 : ℝ), (4268922512649/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5350681529/10000000000 : ℝ)|^2127 ≤ (43884102489021/100000000000000 : ℝ)^1615
        have hw : |(5350681529/10000000000 : ℝ)|=(5350681529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2177103871/10000000000 : ℝ)|^2127 ≤ (1678334045173/12500000000000 : ℝ)^1615
        have hw : |(-2177103871/10000000000 : ℝ)|=(2177103871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5239695741/10000000000 : ℝ)|^2127 ≤ (4268922512649/10000000000000 : ℝ)^1615
        have hw : |(5239695741/10000000000 : ℝ)|=(5239695741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1294_s4_2 (p : ℝ) (hpa : (4253/1024 : ℝ) ≤ p) (hpb : p ≤ (2127/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2675340761/5000000000 : ℝ)*x 0 + (5239695439/10000000000 : ℝ)*x 1 + (-2177104281/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2675340761/5000000000 : ℝ)^2127 ≤ (43884102413409/100000000000000 : ℝ)^1615 := by
    have hnat : (2675340761 : ℕ)^2127*100000000000000^1615 ≤ 43884102413409^1615*5000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2675340761 5000000000 43884102413409 100000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5239695439/10000000000 : ℝ)^2127 ≤ (21344610942987/50000000000000 : ℝ)^1615 := by
    have hnat : (5239695439 : ℕ)^2127*50000000000000^1615 ≤ 21344610942987^1615*10000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5239695439 10000000000 21344610942987 50000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2177104281/10000000000 : ℝ)^2127 ≤ (13426675691567/100000000000000 : ℝ)^1615 := by
    have hnat : (2177104281 : ℕ)^2127*100000000000000^1615 ≤ 13426675691567^1615*10000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2177104281 10000000000 13426675691567 100000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2127/512 : ℝ)) 2127 1615 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2675340761/5000000000 : ℝ), (5239695439/10000000000 : ℝ), (-2177104281/10000000000 : ℝ)] ![(43884102413409/100000000000000 : ℝ), (21344610942987/50000000000000 : ℝ), (13426675691567/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2675340761/5000000000 : ℝ)|^2127 ≤ (43884102413409/100000000000000 : ℝ)^1615
        have hw : |(2675340761/5000000000 : ℝ)|=(2675340761/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5239695439/10000000000 : ℝ)|^2127 ≤ (21344610942987/50000000000000 : ℝ)^1615
        have hw : |(5239695439/10000000000 : ℝ)|=(5239695439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2177104281/10000000000 : ℝ)|^2127 ≤ (13426675691567/100000000000000 : ℝ)^1615
        have hw : |(-2177104281/10000000000 : ℝ)|=(2177104281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1294_s4_3 (p : ℝ) (hpa : (4253/1024 : ℝ) ≤ p) (hpb : p ≤ (2127/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4237379/9765625 : ℝ)*x 0 + (2079319167/5000000000 : ℝ)*x 1 + (1131744507/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4237379/9765625 : ℝ)^2127 ≤ (6659967230237/20000000000000 : ℝ)^1615 := by
    have hnat : (4237379 : ℕ)^2127*20000000000000^1615 ≤ 6659967230237^1615*9765625^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4237379 9765625 6659967230237 20000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2079319167/5000000000 : ℝ)^2127 ≤ (125952862417/400000000000 : ℝ)^1615 := by
    have hnat : (2079319167 : ℕ)^2127*400000000000^1615 ≤ 125952862417^1615*5000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2079319167 5000000000 125952862417 400000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1131744507/2500000000 : ℝ)^2127 ≤ (4401493529107/12500000000000 : ℝ)^1615 := by
    have hnat : (1131744507 : ℕ)^2127*12500000000000^1615 ≤ 4401493529107^1615*2500000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1131744507 2500000000 4401493529107 12500000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2127/512 : ℝ)) 2127 1615 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4237379/9765625 : ℝ), (2079319167/5000000000 : ℝ), (1131744507/2500000000 : ℝ)] ![(6659967230237/20000000000000 : ℝ), (125952862417/400000000000 : ℝ), (4401493529107/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4237379/9765625 : ℝ)|^2127 ≤ (6659967230237/20000000000000 : ℝ)^1615
        have hw : |(4237379/9765625 : ℝ)|=(4237379/9765625 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2079319167/5000000000 : ℝ)|^2127 ≤ (125952862417/400000000000 : ℝ)^1615
        have hw : |(2079319167/5000000000 : ℝ)|=(2079319167/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1131744507/2500000000 : ℝ)|^2127 ≤ (4401493529107/12500000000000 : ℝ)^1615
        have hw : |(1131744507/2500000000 : ℝ)|=(1131744507/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1294_s4_4 (p : ℝ) (hpa : (4253/1024 : ℝ) ≤ p) (hpb : p ≤ (2127/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-417152453/2000000000 : ℝ)*x 0 + (5240359967/10000000000 : ℝ)*x 1 + (5418110809/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (417152453/2000000000 : ℝ)^2127 ≤ (12689741688989/100000000000000 : ℝ)^1615 := by
    have hnat : (417152453 : ℕ)^2127*100000000000000^1615 ≤ 12689741688989^1615*2000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      417152453 2000000000 12689741688989 100000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5240359967/10000000000 : ℝ)^2127 ≤ (2668522033553/6250000000000 : ℝ)^1615 := by
    have hnat : (5240359967 : ℕ)^2127*6250000000000^1615 ≤ 2668522033553^1615*10000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5240359967 10000000000 2668522033553 6250000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5418110809/10000000000 : ℝ)^2127 ≤ (44613905768637/100000000000000 : ℝ)^1615 := by
    have hnat : (5418110809 : ℕ)^2127*100000000000000^1615 ≤ 44613905768637^1615*10000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5418110809 10000000000 44613905768637 100000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2127/512 : ℝ)) 2127 1615 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-417152453/2000000000 : ℝ), (5240359967/10000000000 : ℝ), (5418110809/10000000000 : ℝ)] ![(12689741688989/100000000000000 : ℝ), (2668522033553/6250000000000 : ℝ), (44613905768637/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-417152453/2000000000 : ℝ)|^2127 ≤ (12689741688989/100000000000000 : ℝ)^1615
        have hw : |(-417152453/2000000000 : ℝ)|=(417152453/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5240359967/10000000000 : ℝ)|^2127 ≤ (2668522033553/6250000000000 : ℝ)^1615
        have hw : |(5240359967/10000000000 : ℝ)|=(5240359967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5418110809/10000000000 : ℝ)|^2127 ≤ (44613905768637/100000000000000 : ℝ)^1615
        have hw : |(5418110809/10000000000 : ℝ)|=(5418110809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1294_s4_5 (p : ℝ) (hpa : (4253/1024 : ℝ) ≤ p) (hpb : p ≤ (2127/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2652410007/5000000000 : ℝ)*x 0 + (-199868869/1000000000 : ℝ)*x 1 + (2709055331/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652410007/5000000000 : ℝ)^2127 ≤ (43389393425497/100000000000000 : ℝ)^1615 := by
    have hnat : (2652410007 : ℕ)^2127*100000000000000^1615 ≤ 43389393425497^1615*5000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652410007 5000000000 43389393425497 100000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (199868869/1000000000 : ℝ)^2127 ≤ (11996702389893/100000000000000 : ℝ)^1615 := by
    have hnat : (199868869 : ℕ)^2127*100000000000000^1615 ≤ 11996702389893^1615*1000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      199868869 1000000000 11996702389893 100000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2709055331/5000000000 : ℝ)^2127 ≤ (44613904174467/100000000000000 : ℝ)^1615 := by
    have hnat : (2709055331 : ℕ)^2127*100000000000000^1615 ≤ 44613904174467^1615*5000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2709055331 5000000000 44613904174467 100000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2127/512 : ℝ)) 2127 1615 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652410007/5000000000 : ℝ), (-199868869/1000000000 : ℝ), (2709055331/5000000000 : ℝ)] ![(43389393425497/100000000000000 : ℝ), (11996702389893/100000000000000 : ℝ), (44613904174467/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652410007/5000000000 : ℝ)|^2127 ≤ (43389393425497/100000000000000 : ℝ)^1615
        have hw : |(2652410007/5000000000 : ℝ)|=(2652410007/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-199868869/1000000000 : ℝ)|^2127 ≤ (11996702389893/100000000000000 : ℝ)^1615
        have hw : |(-199868869/1000000000 : ℝ)|=(199868869/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2709055331/5000000000 : ℝ)|^2127 ≤ (44613904174467/100000000000000 : ℝ)^1615
        have hw : |(2709055331/5000000000 : ℝ)|=(2709055331/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1294_s4_6 (p : ℝ) (hpa : (4253/1024 : ℝ) ≤ p) (hpb : p ≤ (2127/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1326204907/2500000000 : ℝ)*x 0 + (5418111081/10000000000 : ℝ)*x 1 + (-3122951/15625000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1326204907/2500000000 : ℝ)^2127 ≤ (21694694633697/50000000000000 : ℝ)^1615 := by
    have hnat : (1326204907 : ℕ)^2127*50000000000000^1615 ≤ 21694694633697^1615*2500000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1326204907 2500000000 21694694633697 50000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5418111081/10000000000 : ℝ)^2127 ≤ (22306954359197/50000000000000 : ℝ)^1615 := by
    have hnat : (5418111081 : ℕ)^2127*50000000000000^1615 ≤ 22306954359197^1615*10000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5418111081 10000000000 22306954359197 50000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3122951/15625000 : ℝ)^2127 ≤ (5998350997317/50000000000000 : ℝ)^1615 := by
    have hnat : (3122951 : ℕ)^2127*50000000000000^1615 ≤ 5998350997317^1615*15625000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3122951 15625000 5998350997317 50000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2127/512 : ℝ)) 2127 1615 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1326204907/2500000000 : ℝ), (5418111081/10000000000 : ℝ), (-3122951/15625000 : ℝ)] ![(21694694633697/50000000000000 : ℝ), (22306954359197/50000000000000 : ℝ), (5998350997317/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1326204907/2500000000 : ℝ)|^2127 ≤ (21694694633697/50000000000000 : ℝ)^1615
        have hw : |(1326204907/2500000000 : ℝ)|=(1326204907/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5418111081/10000000000 : ℝ)|^2127 ≤ (22306954359197/50000000000000 : ℝ)^1615
        have hw : |(5418111081/10000000000 : ℝ)|=(5418111081/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3122951/15625000 : ℝ)|^2127 ≤ (5998350997317/50000000000000 : ℝ)^1615
        have hw : |(-3122951/15625000 : ℝ)|=(3122951/15625000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1294_s4_7 (p : ℝ) (hpa : (4253/1024 : ℝ) ≤ p) (hpb : p ≤ (2127/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4339105357/10000000000 : ℝ)*x 0 + (4525611877/10000000000 : ℝ)*x 1 + (520001493/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4339105357/10000000000 : ℝ)^2127 ≤ (8325032976091/25000000000000 : ℝ)^1615 := by
    have hnat : (4339105357 : ℕ)^2127*25000000000000^1615 ≤ 8325032976091^1615*10000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4339105357 10000000000 8325032976091 25000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4525611877/10000000000 : ℝ)^2127 ≤ (4399744227997/12500000000000 : ℝ)^1615 := by
    have hnat : (4525611877 : ℕ)^2127*12500000000000^1615 ≤ 4399744227997^1615*10000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4525611877 10000000000 4399744227997 12500000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (520001493/1250000000 : ℝ)^2127 ≤ (1575095713141/5000000000000 : ℝ)^1615 := by
    have hnat : (520001493 : ℕ)^2127*5000000000000^1615 ≤ 1575095713141^1615*1250000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      520001493 1250000000 1575095713141 5000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2127/512 : ℝ)) 2127 1615 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4339105357/10000000000 : ℝ), (4525611877/10000000000 : ℝ), (520001493/1250000000 : ℝ)] ![(8325032976091/25000000000000 : ℝ), (4399744227997/12500000000000 : ℝ), (1575095713141/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4339105357/10000000000 : ℝ)|^2127 ≤ (8325032976091/25000000000000 : ℝ)^1615
        have hw : |(4339105357/10000000000 : ℝ)|=(4339105357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4525611877/10000000000 : ℝ)|^2127 ≤ (4399744227997/12500000000000 : ℝ)^1615
        have hw : |(4525611877/10000000000 : ℝ)|=(4525611877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(520001493/1250000000 : ℝ)|^2127 ≤ (1575095713141/5000000000000 : ℝ)^1615
        have hw : |(520001493/1250000000 : ℝ)|=(520001493/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1294_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4253/1024 : ℝ) ≤ p) (hpb : p ≤ (2127/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152840397/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1883/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10667/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10961/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (59/400 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1883/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10667/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1883/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10667/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1883/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10667/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1883/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10667/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1883/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10667/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1883/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10667/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10667/100000 : ℝ) ^ (4253/1024 : ℝ) ≤ (4593231406157011/50000000000000000000 : ℝ) := by
    have hpowers : (10667/100000 : ℝ)^4253 ≤ (4593231406157011/50000000000000000000 : ℝ)^1024 := by
      have hnat : (10667 : ℕ)^4253*50000000000000000000^1024 ≤ 4593231406157011^1024*100000^4253 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10667 100000 4593231406157011 50000000000000000000 4253 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10667/100000 : ℝ)) (X := (4593231406157011/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4253 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1883/12500 : ℝ) ^ (4253/1024 : ℝ) ≤ (19261618787103/50000000000000000 : ℝ) := by
    have hpowers : (1883/12500 : ℝ)^4253 ≤ (19261618787103/50000000000000000 : ℝ)^1024 := by
      have hnat : (1883 : ℕ)^4253*50000000000000000^1024 ≤ 19261618787103^1024*12500^4253 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1883 12500 19261618787103 50000000000000000 4253 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1883/12500 : ℝ)) (X := (19261618787103/50000000000000000 : ℝ)) (by norm_num) (by norm_num) 4253 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25004593231406157011/25000000000000000000 : ℝ) ≤ (2500110584080551/2500000000000000 : ℝ) ^ (4253/1024 : ℝ) := by
    have hpowers : (25004593231406157011/25000000000000000000 : ℝ)^1024 ≤ (2500110584080551/2500000000000000 : ℝ)^4253 := by
      have hnat : (25004593231406157011 : ℕ)^1024*2500000000000000^4253 ≤ 2500110584080551^4253*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25004593231406157011 25000000000000000000 2500110584080551 2500000000000000 1024 4253 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500110584080551/2500000000000000 : ℝ)) (X := (25004593231406157011/25000000000000000000 : ℝ)) (by norm_num) 4253 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50023854850193260011/50000000000000000000 : ℝ) ≤ (5000574252144941/5000000000000000 : ℝ) ^ (4253/1024 : ℝ) := by
    have hpowers : (50023854850193260011/50000000000000000000 : ℝ)^1024 ≤ (5000574252144941/5000000000000000 : ℝ)^4253 := by
      have hnat : (50023854850193260011 : ℕ)^1024*5000000000000000^4253 ≤ 5000574252144941^4253*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50023854850193260011 50000000000000000000 5000574252144941 5000000000000000 1024 4253 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000574252144941/5000000000000000 : ℝ)) (X := (50023854850193260011/50000000000000000000 : ℝ)) (by norm_num) 4253 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25019261618787103/25000000000000000 : ℝ) ≤ (250046366806439/250000000000000 : ℝ) ^ (4253/1024 : ℝ) := by
    have hpowers : (25019261618787103/25000000000000000 : ℝ)^1024 ≤ (250046366806439/250000000000000 : ℝ)^4253 := by
      have hnat : (25019261618787103 : ℕ)^1024*250000000000000^4253 ≤ 250046366806439^4253*25000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25019261618787103 25000000000000000 250046366806439 250000000000000 1024 4253 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (250046366806439/250000000000000 : ℝ)) (X := (25019261618787103/25000000000000000 : ℝ)) (by norm_num) 4253 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4593231406157011/50000000000000000000 : ℝ) ≤ ((5494609945673286067/5496250000000000000 : ℝ)+2*(353083983839/219850000000000 : ℝ)*(10667/100000 : ℝ))^(4253/1024 : ℝ) := by
    rw [show (5494609945673286067/5496250000000000000 : ℝ)+2*(353083983839/219850000000000 : ℝ)*(10667/100000 : ℝ)=(2500110584080551/2500000000000000 : ℝ) by norm_num, show 1+2*(4593231406157011/50000000000000000000 : ℝ)=(25004593231406157011/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(19261618787103/50000000000000000 : ℝ)+(4593231406157011/50000000000000000000 : ℝ) ≤ ((5494609945673286067/5496250000000000000 : ℝ)+(353083983839/219850000000000 : ℝ)*((1883/12500 : ℝ)+(10667/100000 : ℝ)))^(4253/1024 : ℝ) := by
    rw [show (5494609945673286067/5496250000000000000 : ℝ)+(353083983839/219850000000000 : ℝ)*((1883/12500 : ℝ)+(10667/100000 : ℝ))=(5000574252144941/5000000000000000 : ℝ) by norm_num, show 1+(19261618787103/50000000000000000 : ℝ)+(4593231406157011/50000000000000000000 : ℝ)=(50023854850193260011/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(19261618787103/50000000000000000 : ℝ) ≤ ((5494609945673286067/5496250000000000000 : ℝ)+2*(353083983839/219850000000000 : ℝ)*(1883/12500 : ℝ))^(4253/1024 : ℝ) := by
    rw [show (5494609945673286067/5496250000000000000 : ℝ)+2*(353083983839/219850000000000 : ℝ)*(1883/12500 : ℝ)=(250046366806439/250000000000000 : ℝ) by norm_num, show 1+2*(19261618787103/50000000000000000 : ℝ)=(25019261618787103/25000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5494609945673286067/5496250000000000000 : ℝ)*(X 1 0+X 2 0)+(353083983839/219850000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4253/1024 : ℝ)) (lo := (10667/100000 : ℝ)) (hi := (1883/12500 : ℝ)) (c := (5494609945673286067/5496250000000000000 : ℝ)) (alpha := (353083983839/219850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5494609945673286067/5496250000000000000 : ℝ)*(X 0 1+X 2 1)+(353083983839/219850000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4253/1024 : ℝ)) (lo := (10667/100000 : ℝ)) (hi := (1883/12500 : ℝ)) (c := (5494609945673286067/5496250000000000000 : ℝ)) (alpha := (353083983839/219850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5494609945673286067/5496250000000000000 : ℝ)*(X 0 2+X 1 2)+(353083983839/219850000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4253/1024 : ℝ)) (lo := (10667/100000 : ℝ)) (hi := (1883/12500 : ℝ)) (c := (5494609945673286067/5496250000000000000 : ℝ)) (alpha := (353083983839/219850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-65179627/312500000 : ℝ)*X 0 0+(541877873/1000000000 : ℝ)*X 0 1+(5239695523/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1294_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5350681529/10000000000 : ℝ)*X 1 0+(-2177103871/10000000000 : ℝ)*X 1 1+(5239695741/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1294_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2675340761/5000000000 : ℝ)*X 2 0+(5239695439/10000000000 : ℝ)*X 2 1+(-2177104281/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1294_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4237379/9765625 : ℝ)*X 0 0+(2079319167/5000000000 : ℝ)*X 0 1+(1131744507/2500000000 : ℝ)*X 0 2+(4237379/9765625 : ℝ)*X 1 0+(2079319167/5000000000 : ℝ)*X 1 1+(1131744507/2500000000 : ℝ)*X 1 2+(4237379/9765625 : ℝ)*X 2 0+(2079319167/5000000000 : ℝ)*X 2 1+(1131744507/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1294_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-417152453/2000000000 : ℝ)*X 0 0+(5240359967/10000000000 : ℝ)*X 0 1+(5418110809/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1294_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2652410007/5000000000 : ℝ)*X 1 0+(-199868869/1000000000 : ℝ)*X 1 1+(2709055331/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1294_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1326204907/2500000000 : ℝ)*X 2 0+(5418111081/10000000000 : ℝ)*X 2 1+(-3122951/15625000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1294_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4339105357/10000000000 : ℝ)*X 0 0+(4525611877/10000000000 : ℝ)*X 0 1+(520001493/1250000000 : ℝ)*X 0 2+(4339105357/10000000000 : ℝ)*X 1 0+(4525611877/10000000000 : ℝ)*X 1 1+(520001493/1250000000 : ℝ)*X 1 2+(4339105357/10000000000 : ℝ)*X 2 0+(4525611877/10000000000 : ℝ)*X 2 1+(520001493/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1294_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (535099829009811755319334521/274812500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (628370083/100000000000000 : ℝ)*(base19) + (17833109/3125000000000 : ℝ)*(base23) + (6455479/50000000000000 : ℝ)*(upper2) + (4755999/3125000000000 : ℝ)*(upper3) + (4149467577992589/100000000000000 : ℝ)*(major0) + (4149467577992589/100000000000000 : ℝ)*(major1) + (414946757799259/10000000000000 : ℝ)*(major2) + (279200882565423/5000000000000 : ℝ)*(sp0) + (5584032081245883/100000000000000 : ℝ)*(sp1) + (1396005860753577/25000000000000 : ℝ)*(sp2) + (2714892883755237/100000000000000 : ℝ)*(sp3) + (15058307507/100000000000000 : ℝ)*(sp4) + (8695942171/100000000000000 : ℝ)*(sp6) + (1187213641/12500000000000 : ℝ)*(sp7) + (542980476292873/20000000000000 : ℝ)*(f.failure) + (5584032709615967/100000000000000 : ℝ)*(f.sum) + (15464764851753/2748125000000000000000000000 : ℝ)*base66 + (422229797140667537/549625000000000000000000000000000 : ℝ)*base68 + (498400652180964353/54962500000000000000000000000000 : ℝ)*base69 + (2484785155286332463/549625000000000000000000000000000 : ℝ)*base71 + (21651786427501/5496250000000000000000000000 : ℝ)*base74 + (1199045203251964353/54962500000000000000000000000000 : ℝ)*base75 + (4127276657111732463/549625000000000000000000000000000 : ℝ)*base77 + (3804237935311107463/549625000000000000000000000000000 : ℝ)*base79 + (25162346504729/10992500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (17590581/2000000000000000000000 : ℝ)*base89 + (17590581/2000000000000000000000 : ℝ)*base91 + (2409419/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1311430250025810968724717/549625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (28968407/3125000000000 : ℝ)*(base19) + (542340769/100000000000000 : ℝ)*(base23) + (69226807/100000000000000 : ℝ)*(upper3) + (2114993/50000000000000 : ℝ)*(lower4) + (130641864251/3125000000 : ℝ)*(major0) + (130641864251/3125000000 : ℝ)*(major1) + (130641864251/3125000000 : ℝ)*(major2) + (15290725213/100000000000000 : ℝ)*(sp1) + (172265667/1000000000000 : ℝ)*(sp2) + (140747839/12500000000000 : ℝ)*(sp3) + (2812923548101649/50000000000000 : ℝ)*(sp4) + (5625830878489061/100000000000000 : ℝ)*(sp5) + (562582932729583/10000000000000 : ℝ)*(sp6) + (683807752585783/25000000000000 : ℝ)*(sp7) + (683808034081461/25000000000000 : ℝ)*(f.failure) + (2812923548101649/50000000000000 : ℝ)*(f.sum) + (1247198452841/2198500000000000000000000000 : ℝ)*base66 + (1468942327346053/274812500000000000000000000000 : ℝ)*base68 + (3000977189629553/274812500000000000000000000000 : ℝ)*base70 + (556654276541231/549625000000000000000000000000 : ℝ)*base72 + (13747113357523/4397000000000000000000000000 : ℝ)*base74 + (6802559113109231/549625000000000000000000000000 : ℝ)*base76 + (1410241611206339/137406250000000000000000000000 : ℝ)*base78 + (4045255202002803/274812500000000000000000000000 : ℝ)*base80 + (5094189768617/1099250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (29580017/2500000000000000000000 : ℝ)*base89 + (29580017/2500000000000000000000 : ℝ)*base91 + (29580017/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1294_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4253/1024 : ℝ) ≤ p) (hpb : p ≤ (2127/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152840397/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1883/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10667/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10961/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (59/400 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1294_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1294_s5_0 (p : ℝ) (hpa : (4253/1024 : ℝ) ≤ p) (hpb : p ≤ (2127/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2086103201/10000000000 : ℝ)*x 0 + (676971553/1250000000 : ℝ)*x 1 + (1310617081/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2086103201/10000000000 : ℝ)^2127 ≤ (12692473603171/100000000000000 : ℝ)^1615 := by
    have hnat : (2086103201 : ℕ)^2127*100000000000000^1615 ≤ 12692473603171^1615*10000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2086103201 10000000000 12692473603171 100000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (676971553/1250000000 : ℝ)^2127 ≤ (44588548432513/100000000000000 : ℝ)^1615 := by
    have hnat : (676971553 : ℕ)^2127*100000000000000^1615 ≤ 44588548432513^1615*1250000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      676971553 1250000000 44588548432513 100000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1310617081/2500000000 : ℝ)^2127 ≤ (10679744486773/25000000000000 : ℝ)^1615 := by
    have hnat : (1310617081 : ℕ)^2127*25000000000000^1615 ≤ 10679744486773^1615*2500000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310617081 2500000000 10679744486773 25000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2127/512 : ℝ)) 2127 1615 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2086103201/10000000000 : ℝ), (676971553/1250000000 : ℝ), (1310617081/2500000000 : ℝ)] ![(12692473603171/100000000000000 : ℝ), (44588548432513/100000000000000 : ℝ), (10679744486773/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2086103201/10000000000 : ℝ)|^2127 ≤ (12692473603171/100000000000000 : ℝ)^1615
        have hw : |(-2086103201/10000000000 : ℝ)|=(2086103201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(676971553/1250000000 : ℝ)|^2127 ≤ (44588548432513/100000000000000 : ℝ)^1615
        have hw : |(676971553/1250000000 : ℝ)|=(676971553/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1310617081/2500000000 : ℝ)|^2127 ≤ (10679744486773/25000000000000 : ℝ)^1615
        have hw : |(1310617081/2500000000 : ℝ)|=(1310617081/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1294_s5_1 (p : ℝ) (hpa : (4253/1024 : ℝ) ≤ p) (hpb : p ≤ (2127/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5349918363/10000000000 : ℝ)*x 0 + (-2174454877/10000000000 : ℝ)*x 1 + (5242468561/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349918363/10000000000 : ℝ)^2127 ≤ (43875859166809/100000000000000 : ℝ)^1615 := by
    have hnat : (5349918363 : ℕ)^2127*100000000000000^1615 ≤ 43875859166809^1615*10000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349918363 10000000000 43875859166809 100000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2174454877/10000000000 : ℝ)^2127 ≤ (1340516033189/10000000000000 : ℝ)^1615 := by
    have hnat : (2174454877 : ℕ)^2127*10000000000000^1615 ≤ 1340516033189^1615*10000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2174454877 10000000000 1340516033189 10000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5242468561/10000000000 : ℝ)^2127 ≤ (10679745122643/25000000000000 : ℝ)^1615 := by
    have hnat : (5242468561 : ℕ)^2127*25000000000000^1615 ≤ 10679745122643^1615*10000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242468561 10000000000 10679745122643 25000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2127/512 : ℝ)) 2127 1615 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349918363/10000000000 : ℝ), (-2174454877/10000000000 : ℝ), (5242468561/10000000000 : ℝ)] ![(43875859166809/100000000000000 : ℝ), (1340516033189/10000000000000 : ℝ), (10679745122643/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349918363/10000000000 : ℝ)|^2127 ≤ (43875859166809/100000000000000 : ℝ)^1615
        have hw : |(5349918363/10000000000 : ℝ)|=(5349918363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2174454877/10000000000 : ℝ)|^2127 ≤ (1340516033189/10000000000000 : ℝ)^1615
        have hw : |(-2174454877/10000000000 : ℝ)|=(2174454877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5242468561/10000000000 : ℝ)|^2127 ≤ (10679745122643/25000000000000 : ℝ)^1615
        have hw : |(5242468561/10000000000 : ℝ)|=(5242468561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1294_s5_2 (p : ℝ) (hpa : (4253/1024 : ℝ) ≤ p) (hpb : p ≤ (2127/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5349918177/10000000000 : ℝ)*x 0 + (104849371/200000000 : ℝ)*x 1 + (-1087227569/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349918177/10000000000 : ℝ)^2127 ≤ (43875857157779/100000000000000 : ℝ)^1615 := by
    have hnat : (5349918177 : ℕ)^2127*100000000000000^1615 ≤ 43875857157779^1615*10000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349918177 10000000000 43875857157779 100000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (104849371/200000000 : ℝ)^2127 ≤ (42718980372521/100000000000000 : ℝ)^1615 := by
    have hnat : (104849371 : ℕ)^2127*100000000000000^1615 ≤ 42718980372521^1615*200000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      104849371 200000000 42718980372521 100000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1087227569/5000000000 : ℝ)^2127 ≤ (13405162451017/100000000000000 : ℝ)^1615 := by
    have hnat : (1087227569 : ℕ)^2127*100000000000000^1615 ≤ 13405162451017^1615*5000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1087227569 5000000000 13405162451017 100000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2127/512 : ℝ)) 2127 1615 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349918177/10000000000 : ℝ), (104849371/200000000 : ℝ), (-1087227569/5000000000 : ℝ)] ![(43875857157779/100000000000000 : ℝ), (42718980372521/100000000000000 : ℝ), (13405162451017/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349918177/10000000000 : ℝ)|^2127 ≤ (43875857157779/100000000000000 : ℝ)^1615
        have hw : |(5349918177/10000000000 : ℝ)|=(5349918177/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(104849371/200000000 : ℝ)|^2127 ≤ (42718980372521/100000000000000 : ℝ)^1615
        have hw : |(104849371/200000000 : ℝ)|=(104849371/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1087227569/5000000000 : ℝ)|^2127 ≤ (13405162451017/100000000000000 : ℝ)^1615
        have hw : |(-1087227569/5000000000 : ℝ)|=(1087227569/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1294_s5_3 (p : ℝ) (hpa : (4253/1024 : ℝ) ≤ p) (hpb : p ≤ (2127/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2169643371/5000000000 : ℝ)*x 0 + (2082277353/5000000000 : ℝ)*x 1 + (4521008333/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2169643371/5000000000 : ℝ)^2127 ≤ (4162745656577/12500000000000 : ℝ)^1615 := by
    have hnat : (2169643371 : ℕ)^2127*12500000000000^1615 ≤ 4162745656577^1615*5000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2169643371 5000000000 4162745656577 12500000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2082277353/5000000000 : ℝ)^2127 ≤ (3154722826963/10000000000000 : ℝ)^1615 := by
    have hnat : (2082277353 : ℕ)^2127*10000000000000^1615 ≤ 3154722826963^1615*5000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2082277353 5000000000 3154722826963 10000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4521008333/10000000000 : ℝ)^2127 ≤ (35150806469977/100000000000000 : ℝ)^1615 := by
    have hnat : (4521008333 : ℕ)^2127*100000000000000^1615 ≤ 35150806469977^1615*10000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4521008333 10000000000 35150806469977 100000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2127/512 : ℝ)) 2127 1615 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2169643371/5000000000 : ℝ), (2082277353/5000000000 : ℝ), (4521008333/10000000000 : ℝ)] ![(4162745656577/12500000000000 : ℝ), (3154722826963/10000000000000 : ℝ), (35150806469977/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2169643371/5000000000 : ℝ)|^2127 ≤ (4162745656577/12500000000000 : ℝ)^1615
        have hw : |(2169643371/5000000000 : ℝ)|=(2169643371/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2082277353/5000000000 : ℝ)|^2127 ≤ (3154722826963/10000000000000 : ℝ)^1615
        have hw : |(2082277353/5000000000 : ℝ)|=(2082277353/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4521008333/10000000000 : ℝ)|^2127 ≤ (35150806469977/100000000000000 : ℝ)^1615
        have hw : |(4521008333/10000000000 : ℝ)|=(4521008333/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1294_s5_4 (p : ℝ) (hpa : (4253/1024 : ℝ) ≤ p) (hpb : p ≤ (2127/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2086116933/10000000000 : ℝ)*x 0 + (5243090383/10000000000 : ℝ)*x 1 + (216605863/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2086116933/10000000000 : ℝ)^2127 ≤ (12692583640411/100000000000000 : ℝ)^1615 := by
    have hnat : (2086116933 : ℕ)^2127*100000000000000^1615 ≤ 12692583640411^1615*10000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2086116933 10000000000 12692583640411 100000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5243090383/10000000000 : ℝ)^2127 ≤ (8545130799933/20000000000000 : ℝ)^1615 := by
    have hnat : (5243090383 : ℕ)^2127*20000000000000^1615 ≤ 8545130799933^1615*10000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243090383 10000000000 8545130799933 20000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (216605863/400000000 : ℝ)^2127 ≤ (22290881172173/50000000000000 : ℝ)^1615 := by
    have hnat : (216605863 : ℕ)^2127*50000000000000^1615 ≤ 22290881172173^1615*400000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216605863 400000000 22290881172173 50000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2127/512 : ℝ)) 2127 1615 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2086116933/10000000000 : ℝ), (5243090383/10000000000 : ℝ), (216605863/400000000 : ℝ)] ![(12692583640411/100000000000000 : ℝ), (8545130799933/20000000000000 : ℝ), (22290881172173/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2086116933/10000000000 : ℝ)|^2127 ≤ (12692583640411/100000000000000 : ℝ)^1615
        have hw : |(-2086116933/10000000000 : ℝ)|=(2086116933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5243090383/10000000000 : ℝ)|^2127 ≤ (8545130799933/20000000000000 : ℝ)^1615
        have hw : |(5243090383/10000000000 : ℝ)|=(5243090383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(216605863/400000000 : ℝ)|^2127 ≤ (22290881172173/50000000000000 : ℝ)^1615
        have hw : |(216605863/400000000 : ℝ)|=(216605863/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1294_s5_5 (p : ℝ) (hpa : (4253/1024 : ℝ) ≤ p) (hpb : p ≤ (2127/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2652768451/5000000000 : ℝ)*x 0 + (-2001776929/10000000000 : ℝ)*x 1 + (5415146583/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652768451/5000000000 : ℝ)^2127 ≤ (43397116113723/100000000000000 : ℝ)^1615 := by
    have hnat : (2652768451 : ℕ)^2127*100000000000000^1615 ≤ 43397116113723^1615*5000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652768451 5000000000 43397116113723 100000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2001776929/10000000000 : ℝ)^2127 ≤ (1502640181053/12500000000000 : ℝ)^1615 := by
    have hnat : (2001776929 : ℕ)^2127*12500000000000^1615 ≤ 1502640181053^1615*10000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2001776929 10000000000 1502640181053 12500000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5415146583/10000000000 : ℝ)^2127 ≤ (2786360151943/6250000000000 : ℝ)^1615 := by
    have hnat : (5415146583 : ℕ)^2127*6250000000000^1615 ≤ 2786360151943^1615*10000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5415146583 10000000000 2786360151943 6250000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2127/512 : ℝ)) 2127 1615 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652768451/5000000000 : ℝ), (-2001776929/10000000000 : ℝ), (5415146583/10000000000 : ℝ)] ![(43397116113723/100000000000000 : ℝ), (1502640181053/12500000000000 : ℝ), (2786360151943/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652768451/5000000000 : ℝ)|^2127 ≤ (43397116113723/100000000000000 : ℝ)^1615
        have hw : |(2652768451/5000000000 : ℝ)|=(2652768451/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2001776929/10000000000 : ℝ)|^2127 ≤ (1502640181053/12500000000000 : ℝ)^1615
        have hw : |(-2001776929/10000000000 : ℝ)|=(2001776929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5415146583/10000000000 : ℝ)|^2127 ≤ (2786360151943/6250000000000 : ℝ)^1615
        have hw : |(5415146583/10000000000 : ℝ)|=(5415146583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1294_s5_6 (p : ℝ) (hpa : (4253/1024 : ℝ) ≤ p) (hpb : p ≤ (2127/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1326384231/2500000000 : ℝ)*x 0 + (1353786641/2500000000 : ℝ)*x 1 + (-500444231/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1326384231/2500000000 : ℝ)^2127 ≤ (10849279087681/25000000000000 : ℝ)^1615 := by
    have hnat : (1326384231 : ℕ)^2127*25000000000000^1615 ≤ 10849279087681^1615*2500000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1326384231 2500000000 10849279087681 25000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1353786641/2500000000 : ℝ)^2127 ≤ (1783270489003/4000000000000 : ℝ)^1615 := by
    have hnat : (1353786641 : ℕ)^2127*4000000000000^1615 ≤ 1783270489003^1615*2500000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1353786641 2500000000 1783270489003 4000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (500444231/2500000000 : ℝ)^2127 ≤ (6010560704439/50000000000000 : ℝ)^1615 := by
    have hnat : (500444231 : ℕ)^2127*50000000000000^1615 ≤ 6010560704439^1615*2500000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      500444231 2500000000 6010560704439 50000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2127/512 : ℝ)) 2127 1615 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1326384231/2500000000 : ℝ), (1353786641/2500000000 : ℝ), (-500444231/2500000000 : ℝ)] ![(10849279087681/25000000000000 : ℝ), (1783270489003/4000000000000 : ℝ), (6010560704439/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1326384231/2500000000 : ℝ)|^2127 ≤ (10849279087681/25000000000000 : ℝ)^1615
        have hw : |(1326384231/2500000000 : ℝ)|=(1326384231/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1353786641/2500000000 : ℝ)|^2127 ≤ (1783270489003/4000000000000 : ℝ)^1615
        have hw : |(1353786641/2500000000 : ℝ)|=(1353786641/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-500444231/2500000000 : ℝ)|^2127 ≤ (6010560704439/50000000000000 : ℝ)^1615
        have hw : |(-500444231/2500000000 : ℝ)|=(500444231/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1294_s5_7 (p : ℝ) (hpa : (4253/1024 : ℝ) ≤ p) (hpb : p ≤ (2127/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4339312967/10000000000 : ℝ)*x 0 + (2259864161/5000000000 : ℝ)*x 1 + (4165841789/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4339312967/10000000000 : ℝ)^2127 ≤ (16651115161861/50000000000000 : ℝ)^1615 := by
    have hnat : (4339312967 : ℕ)^2127*50000000000000^1615 ≤ 16651115161861^1615*10000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4339312967 10000000000 16651115161861 50000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2259864161/5000000000 : ℝ)^2127 ≤ (1756884994837/5000000000000 : ℝ)^1615 := by
    have hnat : (2259864161 : ℕ)^2127*5000000000000^1615 ≤ 1756884994837^1615*5000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2259864161 5000000000 1756884994837 5000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4165841789/10000000000 : ℝ)^2127 ≤ (15780034879967/50000000000000 : ℝ)^1615 := by
    have hnat : (4165841789 : ℕ)^2127*50000000000000^1615 ≤ 15780034879967^1615*10000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4165841789 10000000000 15780034879967 50000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2127/512 : ℝ)) 2127 1615 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4339312967/10000000000 : ℝ), (2259864161/5000000000 : ℝ), (4165841789/10000000000 : ℝ)] ![(16651115161861/50000000000000 : ℝ), (1756884994837/5000000000000 : ℝ), (15780034879967/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4339312967/10000000000 : ℝ)|^2127 ≤ (16651115161861/50000000000000 : ℝ)^1615
        have hw : |(4339312967/10000000000 : ℝ)|=(4339312967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2259864161/5000000000 : ℝ)|^2127 ≤ (1756884994837/5000000000000 : ℝ)^1615
        have hw : |(2259864161/5000000000 : ℝ)|=(2259864161/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4165841789/10000000000 : ℝ)|^2127 ≤ (15780034879967/50000000000000 : ℝ)^1615
        have hw : |(4165841789/10000000000 : ℝ)|=(4165841789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1294_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4253/1024 : ℝ) ≤ p) (hpb : p ≤ (2127/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152840397/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (59/400 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10961/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (551/5000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (459/3125 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (59/400 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10961/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (59/400 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10961/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (59/400 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10961/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (59/400 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10961/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (59/400 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10961/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (59/400 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10961/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10961/100000 : ℝ) ^ (4253/1024 : ℝ) ≤ (2056933426815023/20000000000000000000 : ℝ) := by
    have hpowers : (10961/100000 : ℝ)^4253 ≤ (2056933426815023/20000000000000000000 : ℝ)^1024 := by
      have hnat : (10961 : ℕ)^4253*20000000000000000000^1024 ≤ 2056933426815023^1024*100000^4253 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10961 100000 2056933426815023 20000000000000000000 4253 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10961/100000 : ℝ)) (X := (2056933426815023/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4253 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (59/400 : ℝ) ^ (4253/1024 : ℝ) ≤ (35296123801815837/100000000000000000000 : ℝ) := by
    have hpowers : (59/400 : ℝ)^4253 ≤ (35296123801815837/100000000000000000000 : ℝ)^1024 := by
      have hnat : (59 : ℕ)^4253*100000000000000000000^1024 ≤ 35296123801815837^1024*400^4253 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        59 400 35296123801815837 100000000000000000000 4253 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (59/400 : ℝ)) (X := (35296123801815837/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4253 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10002056933426815023/10000000000000000000 : ℝ) ≤ (500024760585237/500000000000000 : ℝ) ^ (4253/1024 : ℝ) := by
    have hpowers : (10002056933426815023/10000000000000000000 : ℝ)^1024 ≤ (500024760585237/500000000000000 : ℝ)^4253 := by
      have hnat : (10002056933426815023 : ℕ)^1024*500000000000000^4253 ≤ 500024760585237^4253*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002056933426815023 10000000000000000000 500024760585237 500000000000000 1024 4253 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500024760585237/500000000000000 : ℝ)) (X := (10002056933426815023/10000000000000000000 : ℝ)) (by norm_num) 4253 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (12505697598866986369/12500000000000000000 : ℝ) ≤ (10001097264422523/10000000000000000 : ℝ) ^ (4253/1024 : ℝ) := by
    have hpowers : (12505697598866986369/12500000000000000000 : ℝ)^1024 ≤ (10001097264422523/10000000000000000 : ℝ)^4253 := by
      have hnat : (12505697598866986369 : ℕ)^1024*10000000000000000^4253 ≤ 10001097264422523^4253*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12505697598866986369 12500000000000000000 10001097264422523 10000000000000000 1024 4253 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001097264422523/10000000000000000 : ℝ)) (X := (12505697598866986369/12500000000000000000 : ℝ)) (by norm_num) 4253 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50035296123801815837/50000000000000000000 : ℝ) ≤ (5000849658570153/5000000000000000 : ℝ) ^ (4253/1024 : ℝ) := by
    have hpowers : (50035296123801815837/50000000000000000000 : ℝ)^1024 ≤ (5000849658570153/5000000000000000 : ℝ)^4253 := by
      have hnat : (50035296123801815837 : ℕ)^1024*5000000000000000^4253 ≤ 5000849658570153^4253*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50035296123801815837 50000000000000000000 5000849658570153 5000000000000000 1024 4253 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000849658570153/5000000000000000 : ℝ)) (X := (50035296123801815837/50000000000000000000 : ℝ)) (by norm_num) 4253 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2056933426815023/20000000000000000000 : ℝ) ≤ ((6313113026245003489/6315000000000000000 : ℝ)+2*(200684239261/126300000000000 : ℝ)*(10961/100000 : ℝ))^(4253/1024 : ℝ) := by
    rw [show (6313113026245003489/6315000000000000000 : ℝ)+2*(200684239261/126300000000000 : ℝ)*(10961/100000 : ℝ)=(500024760585237/500000000000000 : ℝ) by norm_num, show 1+2*(2056933426815023/20000000000000000000 : ℝ)=(10002056933426815023/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(35296123801815837/100000000000000000000 : ℝ)+(2056933426815023/20000000000000000000 : ℝ) ≤ ((6313113026245003489/6315000000000000000 : ℝ)+(200684239261/126300000000000 : ℝ)*((59/400 : ℝ)+(10961/100000 : ℝ)))^(4253/1024 : ℝ) := by
    rw [show (6313113026245003489/6315000000000000000 : ℝ)+(200684239261/126300000000000 : ℝ)*((59/400 : ℝ)+(10961/100000 : ℝ))=(10001097264422523/10000000000000000 : ℝ) by norm_num, show 1+(35296123801815837/100000000000000000000 : ℝ)+(2056933426815023/20000000000000000000 : ℝ)=(12505697598866986369/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(35296123801815837/100000000000000000000 : ℝ) ≤ ((6313113026245003489/6315000000000000000 : ℝ)+2*(200684239261/126300000000000 : ℝ)*(59/400 : ℝ))^(4253/1024 : ℝ) := by
    rw [show (6313113026245003489/6315000000000000000 : ℝ)+2*(200684239261/126300000000000 : ℝ)*(59/400 : ℝ)=(5000849658570153/5000000000000000 : ℝ) by norm_num, show 1+2*(35296123801815837/100000000000000000000 : ℝ)=(50035296123801815837/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6313113026245003489/6315000000000000000 : ℝ)*(X 1 0+X 2 0)+(200684239261/126300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4253/1024 : ℝ)) (lo := (10961/100000 : ℝ)) (hi := (59/400 : ℝ)) (c := (6313113026245003489/6315000000000000000 : ℝ)) (alpha := (200684239261/126300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6313113026245003489/6315000000000000000 : ℝ)*(X 0 1+X 2 1)+(200684239261/126300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4253/1024 : ℝ)) (lo := (10961/100000 : ℝ)) (hi := (59/400 : ℝ)) (c := (6313113026245003489/6315000000000000000 : ℝ)) (alpha := (200684239261/126300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6313113026245003489/6315000000000000000 : ℝ)*(X 0 2+X 1 2)+(200684239261/126300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4253/1024 : ℝ)) (lo := (10961/100000 : ℝ)) (hi := (59/400 : ℝ)) (c := (6313113026245003489/6315000000000000000 : ℝ)) (alpha := (200684239261/126300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2086103201/10000000000 : ℝ)*X 0 0+(676971553/1250000000 : ℝ)*X 0 1+(1310617081/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1294_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5349918363/10000000000 : ℝ)*X 1 0+(-2174454877/10000000000 : ℝ)*X 1 1+(5242468561/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1294_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5349918177/10000000000 : ℝ)*X 2 0+(104849371/200000000 : ℝ)*X 2 1+(-1087227569/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1294_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2169643371/5000000000 : ℝ)*X 0 0+(2082277353/5000000000 : ℝ)*X 0 1+(4521008333/10000000000 : ℝ)*X 0 2+(2169643371/5000000000 : ℝ)*X 1 0+(2082277353/5000000000 : ℝ)*X 1 1+(4521008333/10000000000 : ℝ)*X 1 2+(2169643371/5000000000 : ℝ)*X 2 0+(2082277353/5000000000 : ℝ)*X 2 1+(4521008333/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1294_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2086116933/10000000000 : ℝ)*X 0 0+(5243090383/10000000000 : ℝ)*X 0 1+(216605863/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1294_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2652768451/5000000000 : ℝ)*X 1 0+(-2001776929/10000000000 : ℝ)*X 1 1+(5415146583/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1294_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1326384231/2500000000 : ℝ)*X 2 0+(1353786641/2500000000 : ℝ)*X 2 1+(-500444231/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1294_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4339312967/10000000000 : ℝ)*X 0 0+(2259864161/5000000000 : ℝ)*X 0 1+(4165841789/10000000000 : ℝ)*X 0 2+(4339312967/10000000000 : ℝ)*X 1 0+(2259864161/5000000000 : ℝ)*X 1 1+(4165841789/10000000000 : ℝ)*X 1 2+(4339312967/10000000000 : ℝ)*X 2 0+(2259864161/5000000000 : ℝ)*X 2 1+(4165841789/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1294_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (82891295633373738910538919/13156250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (66438177/50000000000000 : ℝ)*(base19) + (41414421/12500000000000 : ℝ)*(base23) + (195711961/100000000000000 : ℝ)*(lower2) + (409201579/100000000000000 : ℝ)*(lower4) + (24030661/50000000000000 : ℝ)*(lower5) + (535979200488371/12500000000000 : ℝ)*(major0) + (535979200488371/12500000000000 : ℝ)*(major1) + (428783360390697/10000000000000 : ℝ)*(major2) + (1442555821999869/25000000000000 : ℝ)*(sp0) + (5770234735672839/100000000000000 : ℝ)*(sp1) + (180319829288557/3125000000000 : ℝ)*(sp2) + (2805423874256811/100000000000000 : ℝ)*(sp3) + (2895137429/25000000000000 : ℝ)*(sp4) + (4127495193/50000000000000 : ℝ)*(sp7) + (2805432129247197/100000000000000 : ℝ)*(f.failure) + (5770234868549193/100000000000000 : ℝ)*(f.sum) + (44465474575891/6315000000000000000000000000 : ℝ)*base66 + (333216386939386081/78937500000000000000000000000000 : ℝ)*base68 + (658872662307231833/63150000000000000000000000000000 : ℝ)*base69 + (963313763031051419/78937500000000000000000000000000 : ℝ)*base71 + (908966239763/197343750000000000000000000 : ℝ)*base74 + (1246103528321018167/63150000000000000000000000000000 : ℝ)*base76 + (358340872810174527/26312500000000000000000000000000 : ℝ)*base78 + (329144422454299527/26312500000000000000000000000000 : ℝ)*base80 + (6731073085573/6315000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (100617209/10000000000000000000000 : ℝ)*base89 + (100617209/10000000000000000000000 : ℝ)*base91 + (99382791/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (579166876436385958403149589/52625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (488368497/25000000000000 : ℝ)*(base19) + (1068126883/50000000000000 : ℝ)*(base23) + (224545261/100000000000000 : ℝ)*(upper3) + (71145701/100000000000000 : ℝ)*(lower4) + (228015433/100000000000000 : ℝ)*(upper5) + (2159454517795099/50000000000000 : ℝ)*(major0) + (2159454517795099/50000000000000 : ℝ)*(major1) + (2159454517795099/50000000000000 : ℝ)*(major2) + (39133154441/100000000000000 : ℝ)*(sp1) + (4207202713/10000000000000 : ℝ)*(sp2) + (1162410725201439/20000000000000 : ℝ)*(sp4) + (2906006269689383/50000000000000 : ℝ)*(sp5) + (58120094177263/1000000000000 : ℝ)*(sp6) + (176610254895103/6250000000000 : ℝ)*(sp7) + (176610254895103/6250000000000 : ℝ)*(f.failure) + (1162410725201439/20000000000000 : ℝ)*(f.sum) + (12063052876837/6315000000000000000000000000 : ℝ)*base66 + (675203992578899863/105250000000000000000000000000000 : ℝ)*base68 + (1342140117777100137/105250000000000000000000000000000 : ℝ)*base69 + (751700538898600137/105250000000000000000000000000000 : ℝ)*base71 + (25952829726097/6315000000000000000000000000 : ℝ)*base74 + (877137318393600137/105250000000000000000000000000000 : ℝ)*base75 + (371651188374850137/105250000000000000000000000000000 : ℝ)*base77 + (1213651311407649863/105250000000000000000000000000000 : ℝ)*base80 + (8694812167549/3157500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (1624109/625000000000000000000 : ℝ)*base90 + (1624109/625000000000000000000 : ℝ)*base92 + (1624109/625000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1294_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4253/1024 : ℝ) ≤ p) (hpb : p ≤ (2127/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152840397/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (59/400 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10961/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (551/5000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (459/3125 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1294_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1294_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4253/1024 : ℝ) ≤ p) (hpb : p ≤ (2127/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152840397/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4077/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9519/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (551/5000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (459/3125 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1294_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1294_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1294_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4253/1024 : ℝ) ≤ p) (hpb : p ≤ (2127/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152840397/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4077/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9519/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (551/5000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (459/3125 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1294_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
