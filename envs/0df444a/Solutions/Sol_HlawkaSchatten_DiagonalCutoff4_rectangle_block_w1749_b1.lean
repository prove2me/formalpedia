-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1749_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:19:01.239862+00:00
-- url     : https://prove2.me/submissions/83717090-bf0a-4901-8896-49756b6288ee

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
theorem support_rectangle_w1749_s3_0 (p : ℝ) (hpa : (5743/1024 : ℝ) ≤ p) (hpb : p ≤ (5759/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1227757013/10000000000 : ℝ)*x 0 + (1099672591/2000000000 : ℝ)*x 1 + (1016166953/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1227757013/10000000000 : ℝ)^5759 ≤ (3900247511631/50000000000000 : ℝ)^4735 := by
    have hnat : (1227757013 : ℕ)^5759*50000000000000^4735 ≤ 3900247511631^4735*10000000000^5759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1227757013 10000000000 3900247511631 50000000000000 5759 4735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1099672591/2000000000 : ℝ)^5759 ≤ (24156043170107/50000000000000 : ℝ)^4735 := by
    have hnat : (1099672591 : ℕ)^5759*50000000000000^4735 ≤ 24156043170107^4735*2000000000^5759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1099672591 2000000000 24156043170107 50000000000000 5759 4735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1016166953/2000000000 : ℝ)^5759 ≤ (43887418618207/100000000000000 : ℝ)^4735 := by
    have hnat : (1016166953 : ℕ)^5759*100000000000000^4735 ≤ 43887418618207^4735*2000000000^5759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1016166953 2000000000 43887418618207 100000000000000 5759 4735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5759/1024 : ℝ)) 5759 4735 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1227757013/10000000000 : ℝ), (1099672591/2000000000 : ℝ), (1016166953/2000000000 : ℝ)] ![(3900247511631/50000000000000 : ℝ), (24156043170107/50000000000000 : ℝ), (43887418618207/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1227757013/10000000000 : ℝ)|^5759 ≤ (3900247511631/50000000000000 : ℝ)^4735
        have hw : |(-1227757013/10000000000 : ℝ)|=(1227757013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1099672591/2000000000 : ℝ)|^5759 ≤ (24156043170107/50000000000000 : ℝ)^4735
        have hw : |(1099672591/2000000000 : ℝ)|=(1099672591/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1016166953/2000000000 : ℝ)|^5759 ≤ (43887418618207/100000000000000 : ℝ)^4735
        have hw : |(1016166953/2000000000 : ℝ)|=(1016166953/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1749_s3_1 (p : ℝ) (hpa : (5743/1024 : ℝ) ≤ p) (hpb : p ≤ (5759/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5336980957/10000000000 : ℝ)*x 0 + (-723103971/5000000000 : ℝ)*x 1 + (2540417387/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5336980957/10000000000 : ℝ)^5759 ≤ (372743505761/800000000000 : ℝ)^4735 := by
    have hnat : (5336980957 : ℕ)^5759*800000000000^4735 ≤ 372743505761^4735*10000000000^5759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5336980957 10000000000 372743505761 800000000000 5759 4735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (723103971/5000000000 : ℝ)^5759 ≤ (9519643043787/100000000000000 : ℝ)^4735 := by
    have hnat : (723103971 : ℕ)^5759*100000000000000^4735 ≤ 9519643043787^4735*5000000000^5759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      723103971 5000000000 9519643043787 100000000000000 5759 4735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2540417387/5000000000 : ℝ)^5759 ≤ (1097185467819/2500000000000 : ℝ)^4735 := by
    have hnat : (2540417387 : ℕ)^5759*2500000000000^4735 ≤ 1097185467819^4735*5000000000^5759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2540417387 5000000000 1097185467819 2500000000000 5759 4735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5759/1024 : ℝ)) 5759 4735 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5336980957/10000000000 : ℝ), (-723103971/5000000000 : ℝ), (2540417387/5000000000 : ℝ)] ![(372743505761/800000000000 : ℝ), (9519643043787/100000000000000 : ℝ), (1097185467819/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5336980957/10000000000 : ℝ)|^5759 ≤ (372743505761/800000000000 : ℝ)^4735
        have hw : |(5336980957/10000000000 : ℝ)|=(5336980957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-723103971/5000000000 : ℝ)|^5759 ≤ (9519643043787/100000000000000 : ℝ)^4735
        have hw : |(-723103971/5000000000 : ℝ)|=(723103971/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2540417387/5000000000 : ℝ)|^5759 ≤ (1097185467819/2500000000000 : ℝ)^4735
        have hw : |(2540417387/5000000000 : ℝ)|=(2540417387/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1749_s3_2 (p : ℝ) (hpa : (5743/1024 : ℝ) ≤ p) (hpb : p ≤ (5759/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5336980959/10000000000 : ℝ)*x 0 + (508083477/1000000000 : ℝ)*x 1 + (-289241589/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5336980959/10000000000 : ℝ)^5759 ≤ (46592938241361/100000000000000 : ℝ)^4735 := by
    have hnat : (5336980959 : ℕ)^5759*100000000000000^4735 ≤ 46592938241361^4735*10000000000^5759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5336980959 10000000000 46592938241361 100000000000000 5759 4735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (508083477/1000000000 : ℝ)^5759 ≤ (2742963666921/6250000000000 : ℝ)^4735 := by
    have hnat : (508083477 : ℕ)^5759*6250000000000^4735 ≤ 2742963666921^4735*1000000000^5759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      508083477 1000000000 2742963666921 6250000000000 5759 4735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (289241589/2000000000 : ℝ)^5759 ≤ (1903928613561/20000000000000 : ℝ)^4735 := by
    have hnat : (289241589 : ℕ)^5759*20000000000000^4735 ≤ 1903928613561^4735*2000000000^5759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      289241589 2000000000 1903928613561 20000000000000 5759 4735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5759/1024 : ℝ)) 5759 4735 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5336980959/10000000000 : ℝ), (508083477/1000000000 : ℝ), (-289241589/2000000000 : ℝ)] ![(46592938241361/100000000000000 : ℝ), (2742963666921/6250000000000 : ℝ), (1903928613561/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5336980959/10000000000 : ℝ)|^5759 ≤ (46592938241361/100000000000000 : ℝ)^4735
        have hw : |(5336980959/10000000000 : ℝ)|=(5336980959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(508083477/1000000000 : ℝ)|^5759 ≤ (2742963666921/6250000000000 : ℝ)^4735
        have hw : |(508083477/1000000000 : ℝ)|=(508083477/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-289241589/2000000000 : ℝ)|^5759 ≤ (1903928613561/20000000000000 : ℝ)^4735
        have hw : |(-289241589/2000000000 : ℝ)|=(289241589/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1749_s3_3 (p : ℝ) (hpa : (5743/1024 : ℝ) ≤ p) (hpb : p ≤ (5759/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2011480589/5000000000 : ℝ)*x 0 + (3371546009/10000000000 : ℝ)*x 1 + (947554067/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2011480589/5000000000 : ℝ)^5759 ≤ (33038793689693/100000000000000 : ℝ)^4735 := by
    have hnat : (2011480589 : ℕ)^5759*100000000000000^4735 ≤ 33038793689693^4735*5000000000^5759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2011480589 5000000000 33038793689693 100000000000000 5759 4735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3371546009/10000000000 : ℝ)^5759 ≤ (3331398111239/12500000000000 : ℝ)^4735 := by
    have hnat : (3371546009 : ℕ)^5759*12500000000000^4735 ≤ 3331398111239^4735*10000000000^5759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3371546009 10000000000 3331398111239 12500000000000 5759 4735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (947554067/2000000000 : ℝ)^5759 ≤ (50387526749/125000000000 : ℝ)^4735 := by
    have hnat : (947554067 : ℕ)^5759*125000000000^4735 ≤ 50387526749^4735*2000000000^5759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      947554067 2000000000 50387526749 125000000000 5759 4735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5759/1024 : ℝ)) 5759 4735 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2011480589/5000000000 : ℝ), (3371546009/10000000000 : ℝ), (947554067/2000000000 : ℝ)] ![(33038793689693/100000000000000 : ℝ), (3331398111239/12500000000000 : ℝ), (50387526749/125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2011480589/5000000000 : ℝ)|^5759 ≤ (33038793689693/100000000000000 : ℝ)^4735
        have hw : |(2011480589/5000000000 : ℝ)|=(2011480589/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3371546009/10000000000 : ℝ)|^5759 ≤ (3331398111239/12500000000000 : ℝ)^4735
        have hw : |(3371546009/10000000000 : ℝ)|=(3371546009/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(947554067/2000000000 : ℝ)|^5759 ≤ (50387526749/125000000000 : ℝ)^4735
        have hw : |(947554067/2000000000 : ℝ)|=(947554067/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1749_s3_4 (p : ℝ) (hpa : (5743/1024 : ℝ) ≤ p) (hpb : p ≤ (5759/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-614054819/5000000000 : ℝ)*x 0 + (1271903649/2500000000 : ℝ)*x 1 + (5491441047/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (614054819/5000000000 : ℝ)^5759 ≤ (121925312561/1562500000000 : ℝ)^4735 := by
    have hnat : (614054819 : ℕ)^5759*1562500000000^4735 ≤ 121925312561^4735*5000000000^5759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      614054819 5000000000 121925312561 1562500000000 5759 4735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1271903649/2500000000 : ℝ)^5759 ≤ (43958656921477/100000000000000 : ℝ)^4735 := by
    have hnat : (1271903649 : ℕ)^5759*100000000000000^4735 ≤ 43958656921477^4735*2500000000^5759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1271903649 2500000000 43958656921477 100000000000000 5759 4735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5491441047/10000000000 : ℝ)^5759 ≤ (48238123060029/100000000000000 : ℝ)^4735 := by
    have hnat : (5491441047 : ℕ)^5759*100000000000000^4735 ≤ 48238123060029^4735*10000000000^5759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5491441047 10000000000 48238123060029 100000000000000 5759 4735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5759/1024 : ℝ)) 5759 4735 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-614054819/5000000000 : ℝ), (1271903649/2500000000 : ℝ), (5491441047/10000000000 : ℝ)] ![(121925312561/1562500000000 : ℝ), (43958656921477/100000000000000 : ℝ), (48238123060029/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-614054819/5000000000 : ℝ)|^5759 ≤ (121925312561/1562500000000 : ℝ)^4735
        have hw : |(-614054819/5000000000 : ℝ)|=(614054819/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1271903649/2500000000 : ℝ)|^5759 ≤ (43958656921477/100000000000000 : ℝ)^4735
        have hw : |(1271903649/2500000000 : ℝ)|=(1271903649/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5491441047/10000000000 : ℝ)|^5759 ≤ (48238123060029/100000000000000 : ℝ)^4735
        have hw : |(5491441047/10000000000 : ℝ)|=(5491441047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1749_s3_5 (p : ℝ) (hpa : (5743/1024 : ℝ) ≤ p) (hpb : p ≤ (5759/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5226268501/10000000000 : ℝ)*x 0 + (-1035601663/10000000000 : ℝ)*x 1 + (171607529/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5226268501/10000000000 : ℝ)^5759 ≤ (22710010422539/50000000000000 : ℝ)^4735 := by
    have hnat : (5226268501 : ℕ)^5759*50000000000000^4735 ≤ 22710010422539^4735*10000000000^5759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5226268501 10000000000 22710010422539 50000000000000 5759 4735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1035601663/10000000000 : ℝ)^5759 ≤ (3170928681121/50000000000000 : ℝ)^4735 := by
    have hnat : (1035601663 : ℕ)^5759*50000000000000^4735 ≤ 3170928681121^4735*10000000000^5759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1035601663 10000000000 3170928681121 50000000000000 5759 4735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (171607529/312500000 : ℝ)^5759 ≤ (48238121788641/100000000000000 : ℝ)^4735 := by
    have hnat : (171607529 : ℕ)^5759*100000000000000^4735 ≤ 48238121788641^4735*312500000^5759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      171607529 312500000 48238121788641 100000000000000 5759 4735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5759/1024 : ℝ)) 5759 4735 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5226268501/10000000000 : ℝ), (-1035601663/10000000000 : ℝ), (171607529/312500000 : ℝ)] ![(22710010422539/50000000000000 : ℝ), (3170928681121/50000000000000 : ℝ), (48238121788641/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5226268501/10000000000 : ℝ)|^5759 ≤ (22710010422539/50000000000000 : ℝ)^4735
        have hw : |(5226268501/10000000000 : ℝ)|=(5226268501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1035601663/10000000000 : ℝ)|^5759 ≤ (3170928681121/50000000000000 : ℝ)^4735
        have hw : |(-1035601663/10000000000 : ℝ)|=(1035601663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(171607529/312500000 : ℝ)|^5759 ≤ (48238121788641/100000000000000 : ℝ)^4735
        have hw : |(171607529/312500000 : ℝ)|=(171607529/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1749_s3_6 (p : ℝ) (hpa : (5743/1024 : ℝ) ≤ p) (hpb : p ≤ (5759/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (326641767/625000000 : ℝ)*x 0 + (2745720537/5000000000 : ℝ)*x 1 + (-1035601777/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (326641767/625000000 : ℝ)^5759 ≤ (9084003684901/20000000000000 : ℝ)^4735 := by
    have hnat : (326641767 : ℕ)^5759*20000000000000^4735 ≤ 9084003684901^4735*625000000^5759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      326641767 625000000 9084003684901 20000000000000 5759 4735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2745720537/5000000000 : ℝ)^5759 ≤ (9647624669699/20000000000000 : ℝ)^4735 := by
    have hnat : (2745720537 : ℕ)^5759*20000000000000^4735 ≤ 9647624669699^4735*5000000000^5759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2745720537 5000000000 9647624669699 20000000000000 5759 4735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1035601777/10000000000 : ℝ)^5759 ≤ (792732276417/12500000000000 : ℝ)^4735 := by
    have hnat : (1035601777 : ℕ)^5759*12500000000000^4735 ≤ 792732276417^4735*10000000000^5759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1035601777 10000000000 792732276417 12500000000000 5759 4735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5759/1024 : ℝ)) 5759 4735 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(326641767/625000000 : ℝ), (2745720537/5000000000 : ℝ), (-1035601777/10000000000 : ℝ)] ![(9084003684901/20000000000000 : ℝ), (9647624669699/20000000000000 : ℝ), (792732276417/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(326641767/625000000 : ℝ)|^5759 ≤ (9084003684901/20000000000000 : ℝ)^4735
        have hw : |(326641767/625000000 : ℝ)|=(326641767/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2745720537/5000000000 : ℝ)|^5759 ≤ (9647624669699/20000000000000 : ℝ)^4735
        have hw : |(2745720537/5000000000 : ℝ)|=(2745720537/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1035601777/10000000000 : ℝ)|^5759 ≤ (792732276417/12500000000000 : ℝ)^4735
        have hw : |(-1035601777/10000000000 : ℝ)|=(1035601777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1749_s3_7 (p : ℝ) (hpa : (5743/1024 : ℝ) ≤ p) (hpb : p ≤ (5759/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4024115647/10000000000 : ℝ)*x 0 + (4715585389/10000000000 : ℝ)*x 1 + (3394196677/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4024115647/10000000000 : ℝ)^5759 ≤ (33050325598153/100000000000000 : ℝ)^4735 := by
    have hnat : (4024115647 : ℕ)^5759*100000000000000^4735 ≤ 33050325598153^4735*10000000000^5759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4024115647 10000000000 33050325598153 100000000000000 5759 4735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4715585389/10000000000 : ℝ)^5759 ≤ (4008056283409/10000000000000 : ℝ)^4735 := by
    have hnat : (4715585389 : ℕ)^5759*10000000000000^4735 ≤ 4008056283409^4735*10000000000^5759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4715585389 10000000000 4008056283409 10000000000000 5759 4735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3394196677/10000000000 : ℝ)^5759 ≤ (6717277887823/25000000000000 : ℝ)^4735 := by
    have hnat : (3394196677 : ℕ)^5759*25000000000000^4735 ≤ 6717277887823^4735*10000000000^5759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3394196677 10000000000 6717277887823 25000000000000 5759 4735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5759/1024 : ℝ)) 5759 4735 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4024115647/10000000000 : ℝ), (4715585389/10000000000 : ℝ), (3394196677/10000000000 : ℝ)] ![(33050325598153/100000000000000 : ℝ), (4008056283409/10000000000000 : ℝ), (6717277887823/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4024115647/10000000000 : ℝ)|^5759 ≤ (33050325598153/100000000000000 : ℝ)^4735
        have hw : |(4024115647/10000000000 : ℝ)|=(4024115647/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4715585389/10000000000 : ℝ)|^5759 ≤ (4008056283409/10000000000000 : ℝ)^4735
        have hw : |(4715585389/10000000000 : ℝ)|=(4715585389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3394196677/10000000000 : ℝ)|^5759 ≤ (6717277887823/25000000000000 : ℝ)^4735
        have hw : |(3394196677/10000000000 : ℝ)|=(3394196677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1749_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5743/1024 : ℝ) ≤ p) (hpb : p ≤ (5759/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (53402159/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4499/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4513/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (9027/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3599/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4499/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4513/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4499/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4513/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4499/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4513/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4499/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4513/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4499/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4513/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4499/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4513/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (4513/50000 : ℝ) ^ (5743/1024 : ℝ) ≤ (69338052679061/50000000000000000000 : ℝ) := by
    have hpowers : (4513/50000 : ℝ)^5743 ≤ (69338052679061/50000000000000000000 : ℝ)^1024 := by
      have hnat : (4513 : ℕ)^5743*50000000000000000000^1024 ≤ 69338052679061^1024*50000^5743 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4513 50000 69338052679061 50000000000000000000 5743 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4513/50000 : ℝ)) (X := (69338052679061/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5743 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (4499/25000 : ℝ) ^ (5743/1024 : ℝ) ≤ (3324299616975611/50000000000000000000 : ℝ) := by
    have hpowers : (4499/25000 : ℝ)^5743 ≤ (3324299616975611/50000000000000000000 : ℝ)^1024 := by
      have hnat : (4499 : ℕ)^5743*50000000000000000000^1024 ≤ 3324299616975611^1024*25000^5743 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4499 25000 3324299616975611 50000000000000000000 5743 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4499/25000 : ℝ)) (X := (3324299616975611/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5743 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000069338052679061/25000000000000000000 : ℝ) ≤ (10000004945295841/10000000000000000 : ℝ) ^ (5743/1024 : ℝ) := by
    have hpowers : (25000069338052679061/25000000000000000000 : ℝ)^1024 ≤ (10000004945295841/10000000000000000 : ℝ)^5743 := by
      have hnat : (25000069338052679061 : ℕ)^1024*10000000000000000^5743 ≤ 10000004945295841^5743*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000069338052679061 25000000000000000000 10000004945295841 10000000000000000 1024 5743 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000004945295841/10000000000000000 : ℝ)) (X := (25000069338052679061/25000000000000000000 : ℝ)) (by norm_num) 5743 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (3125212102354353417/3125000000000000000 : ℝ) ≤ (1250015127059349/1250000000000000 : ℝ) ^ (5743/1024 : ℝ) := by
    have hpowers : (3125212102354353417/3125000000000000000 : ℝ)^1024 ≤ (1250015127059349/1250000000000000 : ℝ)^5743 := by
      have hnat : (3125212102354353417 : ℕ)^1024*1250000000000000^5743 ≤ 1250015127059349^5743*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3125212102354353417 3125000000000000000 1250015127059349 1250000000000000 1024 5743 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250015127059349/1250000000000000 : ℝ)) (X := (3125212102354353417/3125000000000000000 : ℝ)) (by norm_num) 5743 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25003324299616975611/25000000000000000000 : ℝ) ≤ (10000237087653743/10000000000000000 : ℝ) ^ (5743/1024 : ℝ) := by
    have hpowers : (25003324299616975611/25000000000000000000 : ℝ)^1024 ≤ (10000237087653743/10000000000000000 : ℝ)^5743 := by
      have hnat : (25003324299616975611 : ℕ)^1024*10000000000000000^5743 ≤ 10000237087653743^5743*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25003324299616975611 25000000000000000000 10000237087653743 10000000000000000 1024 5743 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000237087653743/10000000000000000 : ℝ)) (X := (25003324299616975611/25000000000000000000 : ℝ)) (by norm_num) 5743 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(69338052679061/50000000000000000000 : ℝ) ≤ ((3449921117014664243/3450000000000000000 : ℝ)+2*(8928552227/69000000000000 : ℝ)*(4513/50000 : ℝ))^(5743/1024 : ℝ) := by
    rw [show (3449921117014664243/3450000000000000000 : ℝ)+2*(8928552227/69000000000000 : ℝ)*(4513/50000 : ℝ)=(10000004945295841/10000000000000000 : ℝ) by norm_num, show 1+2*(69338052679061/50000000000000000000 : ℝ)=(25000069338052679061/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3324299616975611/50000000000000000000 : ℝ)+(69338052679061/50000000000000000000 : ℝ) ≤ ((3449921117014664243/3450000000000000000 : ℝ)+(8928552227/69000000000000 : ℝ)*((4499/25000 : ℝ)+(4513/50000 : ℝ)))^(5743/1024 : ℝ) := by
    rw [show (3449921117014664243/3450000000000000000 : ℝ)+(8928552227/69000000000000 : ℝ)*((4499/25000 : ℝ)+(4513/50000 : ℝ))=(1250015127059349/1250000000000000 : ℝ) by norm_num, show 1+(3324299616975611/50000000000000000000 : ℝ)+(69338052679061/50000000000000000000 : ℝ)=(3125212102354353417/3125000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3324299616975611/50000000000000000000 : ℝ) ≤ ((3449921117014664243/3450000000000000000 : ℝ)+2*(8928552227/69000000000000 : ℝ)*(4499/25000 : ℝ))^(5743/1024 : ℝ) := by
    rw [show (3449921117014664243/3450000000000000000 : ℝ)+2*(8928552227/69000000000000 : ℝ)*(4499/25000 : ℝ)=(10000237087653743/10000000000000000 : ℝ) by norm_num, show 1+2*(3324299616975611/50000000000000000000 : ℝ)=(25003324299616975611/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3449921117014664243/3450000000000000000 : ℝ)*(X 1 0+X 2 0)+(8928552227/69000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5743/1024 : ℝ)) (lo := (4513/50000 : ℝ)) (hi := (4499/25000 : ℝ)) (c := (3449921117014664243/3450000000000000000 : ℝ)) (alpha := (8928552227/69000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3449921117014664243/3450000000000000000 : ℝ)*(X 0 1+X 2 1)+(8928552227/69000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5743/1024 : ℝ)) (lo := (4513/50000 : ℝ)) (hi := (4499/25000 : ℝ)) (c := (3449921117014664243/3450000000000000000 : ℝ)) (alpha := (8928552227/69000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3449921117014664243/3450000000000000000 : ℝ)*(X 0 2+X 1 2)+(8928552227/69000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5743/1024 : ℝ)) (lo := (4513/50000 : ℝ)) (hi := (4499/25000 : ℝ)) (c := (3449921117014664243/3450000000000000000 : ℝ)) (alpha := (8928552227/69000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1227757013/10000000000 : ℝ)*X 0 0+(1099672591/2000000000 : ℝ)*X 0 1+(1016166953/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1749_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5336980957/10000000000 : ℝ)*X 1 0+(-723103971/5000000000 : ℝ)*X 1 1+(2540417387/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1749_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5336980959/10000000000 : ℝ)*X 2 0+(508083477/1000000000 : ℝ)*X 2 1+(-289241589/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1749_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2011480589/5000000000 : ℝ)*X 0 0+(3371546009/10000000000 : ℝ)*X 0 1+(947554067/2000000000 : ℝ)*X 0 2+(2011480589/5000000000 : ℝ)*X 1 0+(3371546009/10000000000 : ℝ)*X 1 1+(947554067/2000000000 : ℝ)*X 1 2+(2011480589/5000000000 : ℝ)*X 2 0+(3371546009/10000000000 : ℝ)*X 2 1+(947554067/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1749_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-614054819/5000000000 : ℝ)*X 0 0+(1271903649/2500000000 : ℝ)*X 0 1+(5491441047/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1749_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5226268501/10000000000 : ℝ)*X 1 0+(-1035601663/10000000000 : ℝ)*X 1 1+(171607529/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1749_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((326641767/625000000 : ℝ)*X 2 0+(2745720537/5000000000 : ℝ)*X 2 1+(-1035601777/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1749_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4024115647/10000000000 : ℝ)*X 0 0+(4715585389/10000000000 : ℝ)*X 0 1+(3394196677/10000000000 : ℝ)*X 0 2+(4024115647/10000000000 : ℝ)*X 1 0+(4715585389/10000000000 : ℝ)*X 1 1+(3394196677/10000000000 : ℝ)*X 1 2+(4024115647/10000000000 : ℝ)*X 2 0+(4715585389/10000000000 : ℝ)*X 2 1+(3394196677/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1749_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (41213561270505228680187969/2875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1983988067/100000000000000 : ℝ)*(base19) + (1873315393/100000000000000 : ℝ)*(base23) + (59544811/100000000000000 : ℝ)*(lower2) + (8665907/2500000000000 : ℝ)*(upper3) + (265238633/100000000000000 : ℝ)*(upper5) + (156351650370683/10000000000000 : ℝ)*(major0) + (156351650370683/10000000000000 : ℝ)*(major1) + (156351650370683/10000000000000 : ℝ)*(major2) + (1197531680997703/50000000000000 : ℝ)*(sp0) + (598769189278627/25000000000000 : ℝ)*(sp1) + (1197538433893591/50000000000000 : ℝ)*(sp2) + (365974342147447/50000000000000 : ℝ)*(sp3) + (15379107169/100000000000000 : ℝ)*(sp4) + (39876389/781250000000 : ℝ)*(sp7) + (365976894236343/50000000000000 : ℝ)*(f.failure) + (149692421318911/6250000000000 : ℝ)*(f.sum) + (1996287648721/345000000000000000000000000 : ℝ)*base65 + (12560231166120677/11500000000000000000000000000000 : ℝ)*base68 + (12945936784620677/11500000000000000000000000000000 : ℝ)*base70 + (11698629592120677/11500000000000000000000000000000 : ℝ)*base72 + (638168534731/345000000000000000000000000 : ℝ)*base73 + (30341361863120677/11500000000000000000000000000000 : ℝ)*base76 + (18962171514879323/11500000000000000000000000000000 : ℝ)*base77 + (76761220055120677/11500000000000000000000000000000 : ℝ)*base80 + (898309200061/345000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (2535463/1250000000000000000000 : ℝ)*base90 + (2535463/1250000000000000000000 : ℝ)*base92 + (2535463/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (761924948598406216002873713/57500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (159361883/10000000000000 : ℝ)*(base19) + (1677314633/100000000000000 : ℝ)*(base23) + (2376697/500000000000 : ℝ)*(lower1) + (52024167/25000000000000 : ℝ)*(upper3) + (25488927/25000000000000 : ℝ)*(lower4) + (27675283/10000000000000 : ℝ)*(upper5) + (1616537527446709/100000000000000 : ℝ)*(major0) + (1616537527446709/100000000000000 : ℝ)*(major1) + (1616537527446709/100000000000000 : ℝ)*(major2) + (68051031/50000000000000 : ℝ)*(sp1) + (1238149625810861/50000000000000 : ℝ)*(sp4) + (247629752190083/10000000000000 : ℝ)*(sp5) + (247629757430709/10000000000000 : ℝ)*(sp6) + (756775361576069/100000000000000 : ℝ)*(sp7) + (756775361576069/100000000000000 : ℝ)*(f.failure) + (1238149625810861/50000000000000 : ℝ)*(f.sum) + (2544997996793/3450000000000000000000000000 : ℝ)*base65 + (104292445490825429/115000000000000000000000000000000 : ℝ)*base67 + (933507363680825429/115000000000000000000000000000000 : ℝ)*base69 + (784249420280825429/115000000000000000000000000000000 : ℝ)*base71 + (9899511286207/3450000000000000000000000000 : ℝ)*base74 + (1148068464870825429/115000000000000000000000000000000 : ℝ)*base75 + (167313401059174571/115000000000000000000000000000000 : ℝ)*base78 + (79426994529174571/115000000000000000000000000000000 : ℝ)*base80 + (12862123719593/3450000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (2332971/2500000000000000000000 : ℝ)*base89 + (2332971/2500000000000000000000 : ℝ)*base91 + (2332971/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1749_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5743/1024 : ℝ) ≤ p) (hpb : p ≤ (5759/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (53402159/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4499/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4513/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9027/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3599/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1749_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1749_s4_0 (p : ℝ) (hpa : (5743/1024 : ℝ) ≤ p) (hpb : p ≤ (5759/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1227757257/10000000000 : ℝ)*x 0 + (1374590517/2500000000 : ℝ)*x 1 + (158776109/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1227757257/10000000000 : ℝ)^5759 ≤ (7800496908763/100000000000000 : ℝ)^4735 := by
    have hnat : (1227757257 : ℕ)^5759*100000000000000^4735 ≤ 7800496908763^4735*10000000000^5759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1227757257 10000000000 7800496908763 100000000000000 5759 4735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1374590517/2500000000 : ℝ)^5759 ≤ (48312076860983/100000000000000 : ℝ)^4735 := by
    have hnat : (1374590517 : ℕ)^5759*100000000000000^4735 ≤ 48312076860983^4735*2500000000^5759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1374590517 2500000000 48312076860983 100000000000000 5759 4735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (158776109/312500000 : ℝ)^5759 ≤ (685741034593/1562500000000 : ℝ)^4735 := by
    have hnat : (158776109 : ℕ)^5759*1562500000000^4735 ≤ 685741034593^4735*312500000^5759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      158776109 312500000 685741034593 1562500000000 5759 4735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5759/1024 : ℝ)) 5759 4735 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1227757257/10000000000 : ℝ), (1374590517/2500000000 : ℝ), (158776109/312500000 : ℝ)] ![(7800496908763/100000000000000 : ℝ), (48312076860983/100000000000000 : ℝ), (685741034593/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1227757257/10000000000 : ℝ)|^5759 ≤ (7800496908763/100000000000000 : ℝ)^4735
        have hw : |(-1227757257/10000000000 : ℝ)|=(1227757257/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1374590517/2500000000 : ℝ)|^5759 ≤ (48312076860983/100000000000000 : ℝ)^4735
        have hw : |(1374590517/2500000000 : ℝ)|=(1374590517/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(158776109/312500000 : ℝ)|^5759 ≤ (685741034593/1562500000000 : ℝ)^4735
        have hw : |(158776109/312500000 : ℝ)|=(158776109/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1749_s4_1 (p : ℝ) (hpa : (5743/1024 : ℝ) ≤ p) (hpb : p ≤ (5759/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1334245181/2500000000 : ℝ)*x 0 + (-1446207339/10000000000 : ℝ)*x 1 + (508083547/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1334245181/2500000000 : ℝ)^5759 ≤ (46592935746081/100000000000000 : ℝ)^4735 := by
    have hnat : (1334245181 : ℕ)^5759*100000000000000^4735 ≤ 46592935746081^4735*2500000000^5759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1334245181 2500000000 46592935746081 100000000000000 5759 4735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1446207339/10000000000 : ℝ)^5759 ≤ (4759819108077/50000000000000 : ℝ)^4735 := by
    have hnat : (1446207339 : ℕ)^5759*50000000000000^4735 ≤ 4759819108077^4735*10000000000^5759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1446207339 10000000000 4759819108077 50000000000000 5759 4735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (508083547/1000000000 : ℝ)^5759 ≤ (21943713012423/50000000000000 : ℝ)^4735 := by
    have hnat : (508083547 : ℕ)^5759*50000000000000^4735 ≤ 21943713012423^4735*1000000000^5759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      508083547 1000000000 21943713012423 50000000000000 5759 4735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5759/1024 : ℝ)) 5759 4735 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1334245181/2500000000 : ℝ), (-1446207339/10000000000 : ℝ), (508083547/1000000000 : ℝ)] ![(46592935746081/100000000000000 : ℝ), (4759819108077/50000000000000 : ℝ), (21943713012423/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1334245181/2500000000 : ℝ)|^5759 ≤ (46592935746081/100000000000000 : ℝ)^4735
        have hw : |(1334245181/2500000000 : ℝ)|=(1334245181/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1446207339/10000000000 : ℝ)|^5759 ≤ (4759819108077/50000000000000 : ℝ)^4735
        have hw : |(-1446207339/10000000000 : ℝ)|=(1446207339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(508083547/1000000000 : ℝ)|^5759 ≤ (21943713012423/50000000000000 : ℝ)^4735
        have hw : |(508083547/1000000000 : ℝ)|=(508083547/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1749_s4_2 (p : ℝ) (hpa : (5743/1024 : ℝ) ≤ p) (hpb : p ≤ (5759/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2668490341/5000000000 : ℝ)*x 0 + (5080835501/10000000000 : ℝ)*x 1 + (-723103677/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2668490341/5000000000 : ℝ)^5759 ≤ (11648233825029/25000000000000 : ℝ)^4735 := by
    have hnat : (2668490341 : ℕ)^5759*25000000000000^4735 ≤ 11648233825029^4735*5000000000^5759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2668490341 5000000000 11648233825029 25000000000000 5759 4735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5080835501/10000000000 : ℝ)^5759 ≤ (685741036727/1562500000000 : ℝ)^4735 := by
    have hnat : (5080835501 : ℕ)^5759*1562500000000^4735 ≤ 685741036727^4735*10000000000^5759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5080835501 10000000000 685741036727 1562500000000 5759 4735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (723103677/5000000000 : ℝ)^5759 ≤ (2379909584061/25000000000000 : ℝ)^4735 := by
    have hnat : (723103677 : ℕ)^5759*25000000000000^4735 ≤ 2379909584061^4735*5000000000^5759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      723103677 5000000000 2379909584061 25000000000000 5759 4735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5759/1024 : ℝ)) 5759 4735 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2668490341/5000000000 : ℝ), (5080835501/10000000000 : ℝ), (-723103677/5000000000 : ℝ)] ![(11648233825029/25000000000000 : ℝ), (685741036727/1562500000000 : ℝ), (2379909584061/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2668490341/5000000000 : ℝ)|^5759 ≤ (11648233825029/25000000000000 : ℝ)^4735
        have hw : |(2668490341/5000000000 : ℝ)|=(2668490341/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5080835501/10000000000 : ℝ)|^5759 ≤ (685741036727/1562500000000 : ℝ)^4735
        have hw : |(5080835501/10000000000 : ℝ)|=(5080835501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-723103677/5000000000 : ℝ)|^5759 ≤ (2379909584061/25000000000000 : ℝ)^4735
        have hw : |(-723103677/5000000000 : ℝ)|=(723103677/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1749_s4_3 (p : ℝ) (hpa : (5743/1024 : ℝ) ≤ p) (hpb : p ≤ (5759/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (402296139/1000000000 : ℝ)*x 0 + (3371548559/10000000000 : ℝ)*x 1 + (4737767761/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (402296139/1000000000 : ℝ)^5759 ≤ (412984947591/1250000000000 : ℝ)^4735 := by
    have hnat : (402296139 : ℕ)^5759*1250000000000^4735 ≤ 412984947591^4735*1000000000^5759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      402296139 1000000000 412984947591 1250000000000 5759 4735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3371548559/10000000000 : ℝ)^5759 ≤ (26651209406201/100000000000000 : ℝ)^4735 := by
    have hnat : (3371548559 : ℕ)^5759*100000000000000^4735 ≤ 26651209406201^4735*10000000000^5759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3371548559 10000000000 26651209406201 100000000000000 5759 4735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4737767761/10000000000 : ℝ)^5759 ≤ (20154997381427/50000000000000 : ℝ)^4735 := by
    have hnat : (4737767761 : ℕ)^5759*50000000000000^4735 ≤ 20154997381427^4735*10000000000^5759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4737767761 10000000000 20154997381427 50000000000000 5759 4735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5759/1024 : ℝ)) 5759 4735 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(402296139/1000000000 : ℝ), (3371548559/10000000000 : ℝ), (4737767761/10000000000 : ℝ)] ![(412984947591/1250000000000 : ℝ), (26651209406201/100000000000000 : ℝ), (20154997381427/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(402296139/1000000000 : ℝ)|^5759 ≤ (412984947591/1250000000000 : ℝ)^4735
        have hw : |(402296139/1000000000 : ℝ)|=(402296139/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3371548559/10000000000 : ℝ)|^5759 ≤ (26651209406201/100000000000000 : ℝ)^4735
        have hw : |(3371548559/10000000000 : ℝ)|=(3371548559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4737767761/10000000000 : ℝ)|^5759 ≤ (20154997381427/50000000000000 : ℝ)^4735
        have hw : |(4737767761/10000000000 : ℝ)|=(4737767761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1749_s4_4 (p : ℝ) (hpa : (5743/1024 : ℝ) ≤ p) (hpb : p ≤ (5759/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1228110147/10000000000 : ℝ)*x 0 + (2543807623/5000000000 : ℝ)*x 1 + (137286001/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1228110147/10000000000 : ℝ)^5759 ≤ (3901611968713/50000000000000 : ℝ)^4735 := by
    have hnat : (1228110147 : ℕ)^5759*50000000000000^4735 ≤ 3901611968713^4735*10000000000^5759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1228110147 10000000000 3901611968713 50000000000000 5759 4735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2543807623/5000000000 : ℝ)^5759 ≤ (43958663752263/100000000000000 : ℝ)^4735 := by
    have hnat : (2543807623 : ℕ)^5759*100000000000000^4735 ≤ 43958663752263^4735*5000000000^5759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2543807623 5000000000 43958663752263 100000000000000 5759 4735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (137286001/250000000 : ℝ)^5759 ≤ (48238112301309/100000000000000 : ℝ)^4735 := by
    have hnat : (137286001 : ℕ)^5759*100000000000000^4735 ≤ 48238112301309^4735*250000000^5759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      137286001 250000000 48238112301309 100000000000000 5759 4735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5759/1024 : ℝ)) 5759 4735 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1228110147/10000000000 : ℝ), (2543807623/5000000000 : ℝ), (137286001/250000000 : ℝ)] ![(3901611968713/50000000000000 : ℝ), (43958663752263/100000000000000 : ℝ), (48238112301309/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1228110147/10000000000 : ℝ)|^5759 ≤ (3901611968713/50000000000000 : ℝ)^4735
        have hw : |(-1228110147/10000000000 : ℝ)|=(1228110147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2543807623/5000000000 : ℝ)|^5759 ≤ (43958663752263/100000000000000 : ℝ)^4735
        have hw : |(2543807623/5000000000 : ℝ)|=(2543807623/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(137286001/250000000 : ℝ)|^5759 ≤ (48238112301309/100000000000000 : ℝ)^4735
        have hw : |(137286001/250000000 : ℝ)|=(137286001/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1749_s4_5 (p : ℝ) (hpa : (5743/1024 : ℝ) ≤ p) (hpb : p ≤ (5759/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (402411603/1000000000 : ℝ)*x 0 + (2357791613/5000000000 : ℝ)*x 1 + (3394198601/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (402411603/1000000000 : ℝ)^5759 ≤ (1032822794501/3125000000000 : ℝ)^4735 := by
    have hnat : (402411603 : ℕ)^5759*3125000000000^4735 ≤ 1032822794501^4735*1000000000^5759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      402411603 1000000000 1032822794501 3125000000000 5759 4735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2357791613/5000000000 : ℝ)^5759 ≤ (5010067559197/12500000000000 : ℝ)^4735 := by
    have hnat : (2357791613 : ℕ)^5759*12500000000000^4735 ≤ 5010067559197^4735*5000000000^5759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2357791613 5000000000 5010067559197 12500000000000 5759 4735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3394198601/10000000000 : ℝ)^5759 ≤ (26869130075877/100000000000000 : ℝ)^4735 := by
    have hnat : (3394198601 : ℕ)^5759*100000000000000^4735 ≤ 26869130075877^4735*10000000000^5759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3394198601 10000000000 26869130075877 100000000000000 5759 4735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5759/1024 : ℝ)) 5759 4735 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(402411603/1000000000 : ℝ), (2357791613/5000000000 : ℝ), (3394198601/10000000000 : ℝ)] ![(1032822794501/3125000000000 : ℝ), (5010067559197/12500000000000 : ℝ), (26869130075877/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(402411603/1000000000 : ℝ)|^5759 ≤ (1032822794501/3125000000000 : ℝ)^4735
        have hw : |(402411603/1000000000 : ℝ)|=(402411603/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2357791613/5000000000 : ℝ)|^5759 ≤ (5010067559197/12500000000000 : ℝ)^4735
        have hw : |(2357791613/5000000000 : ℝ)|=(2357791613/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3394198601/10000000000 : ℝ)|^5759 ≤ (26869130075877/100000000000000 : ℝ)^4735
        have hw : |(3394198601/10000000000 : ℝ)|=(3394198601/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1749_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5743/1024 : ℝ) ≤ p) (hpb : p ≤ (5759/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (53402159/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3599/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9027/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2257/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3599/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3599/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9027/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3599/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9027/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3599/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9027/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3599/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9027/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3599/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9027/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3599/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9027/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9027/100000 : ℝ) ^ (5743/1024 : ℝ) ≤ (69381147595243/50000000000000000000 : ℝ) := by
    have hpowers : (9027/100000 : ℝ)^5743 ≤ (69381147595243/50000000000000000000 : ℝ)^1024 := by
      have hnat : (9027 : ℕ)^5743*50000000000000000000^1024 ≤ 69381147595243^1024*100000^5743 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9027 100000 69381147595243 50000000000000000000 5743 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9027/100000 : ℝ)) (X := (69381147595243/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5743 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3599/20000 : ℝ) ^ (5743/1024 : ℝ) ≤ (3323263741793973/50000000000000000000 : ℝ) := by
    have hpowers : (3599/20000 : ℝ)^5743 ≤ (3323263741793973/50000000000000000000 : ℝ)^1024 := by
      have hnat : (3599 : ℕ)^5743*50000000000000000000^1024 ≤ 3323263741793973^1024*20000^5743 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3599 20000 3323263741793973 50000000000000000000 5743 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3599/20000 : ℝ)) (X := (3323263741793973/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5743 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000069381147595243/25000000000000000000 : ℝ) ≤ (10000004948369433/10000000000000000 : ℝ) ^ (5743/1024 : ℝ) := by
    have hpowers : (25000069381147595243/25000000000000000000 : ℝ)^1024 ≤ (10000004948369433/10000000000000000 : ℝ)^5743 := by
      have hnat : (25000069381147595243 : ℕ)^1024*10000000000000000^5743 ≤ 10000004948369433^5743*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000069381147595243 25000000000000000000 10000004948369433 10000000000000000 1024 5743 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000004948369433/10000000000000000 : ℝ)) (X := (25000069381147595243/25000000000000000000 : ℝ)) (by norm_num) 5743 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (1562606020152793413/1562500000000000000 : ℝ) ≤ (10000120981073423/10000000000000000 : ℝ) ^ (5743/1024 : ℝ) := by
    have hpowers : (1562606020152793413/1562500000000000000 : ℝ)^1024 ≤ (10000120981073423/10000000000000000 : ℝ)^5743 := by
      have hnat : (1562606020152793413 : ℕ)^1024*10000000000000000^5743 ≤ 10000120981073423^5743*1562500000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1562606020152793413 1562500000000000000 10000120981073423 10000000000000000 1024 5743 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000120981073423/10000000000000000 : ℝ)) (X := (1562606020152793413/1562500000000000000 : ℝ)) (by norm_num) 5743 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25003323263741793973/25000000000000000000 : ℝ) ≤ (10000237013777413/10000000000000000 : ℝ) ^ (5743/1024 : ℝ) := by
    have hpowers : (25003323263741793973/25000000000000000000 : ℝ)^1024 ≤ (10000237013777413/10000000000000000 : ℝ)^5743 := by
      have hnat : (25003323263741793973 : ℕ)^1024*10000000000000000^5743 ≤ 10000237013777413^5743*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25003323263741793973 25000000000000000000 10000237013777413 10000000000000000 1024 5743 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000237013777413/10000000000000000 : ℝ)) (X := (25003323263741793973/25000000000000000000 : ℝ)) (by norm_num) 5743 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(69381147595243/50000000000000000000 : ℝ) ≤ ((379991311536183219/380000000000000000 : ℝ)+2*(11603270399/89680000000000 : ℝ)*(9027/100000 : ℝ))^(5743/1024 : ℝ) := by
    rw [show (379991311536183219/380000000000000000 : ℝ)+2*(11603270399/89680000000000 : ℝ)*(9027/100000 : ℝ)=(10000004948369433/10000000000000000 : ℝ) by norm_num, show 1+2*(69381147595243/50000000000000000000 : ℝ)=(25000069381147595243/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3323263741793973/50000000000000000000 : ℝ)+(69381147595243/50000000000000000000 : ℝ) ≤ ((379991311536183219/380000000000000000 : ℝ)+(11603270399/89680000000000 : ℝ)*((3599/20000 : ℝ)+(9027/100000 : ℝ)))^(5743/1024 : ℝ) := by
    rw [show (379991311536183219/380000000000000000 : ℝ)+(11603270399/89680000000000 : ℝ)*((3599/20000 : ℝ)+(9027/100000 : ℝ))=(10000120981073423/10000000000000000 : ℝ) by norm_num, show 1+(3323263741793973/50000000000000000000 : ℝ)+(69381147595243/50000000000000000000 : ℝ)=(1562606020152793413/1562500000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3323263741793973/50000000000000000000 : ℝ) ≤ ((379991311536183219/380000000000000000 : ℝ)+2*(11603270399/89680000000000 : ℝ)*(3599/20000 : ℝ))^(5743/1024 : ℝ) := by
    rw [show (379991311536183219/380000000000000000 : ℝ)+2*(11603270399/89680000000000 : ℝ)*(3599/20000 : ℝ)=(10000237013777413/10000000000000000 : ℝ) by norm_num, show 1+2*(3323263741793973/50000000000000000000 : ℝ)=(25003323263741793973/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (379991311536183219/380000000000000000 : ℝ)*(X 1 0+X 2 0)+(11603270399/89680000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5743/1024 : ℝ)) (lo := (9027/100000 : ℝ)) (hi := (3599/20000 : ℝ)) (c := (379991311536183219/380000000000000000 : ℝ)) (alpha := (11603270399/89680000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (379991311536183219/380000000000000000 : ℝ)*(X 0 1+X 2 1)+(11603270399/89680000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5743/1024 : ℝ)) (lo := (9027/100000 : ℝ)) (hi := (3599/20000 : ℝ)) (c := (379991311536183219/380000000000000000 : ℝ)) (alpha := (11603270399/89680000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (379991311536183219/380000000000000000 : ℝ)*(X 0 2+X 1 2)+(11603270399/89680000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5743/1024 : ℝ)) (lo := (9027/100000 : ℝ)) (hi := (3599/20000 : ℝ)) (c := (379991311536183219/380000000000000000 : ℝ)) (alpha := (11603270399/89680000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1227757257/10000000000 : ℝ)*X 0 0+(1374590517/2500000000 : ℝ)*X 0 1+(158776109/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1749_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1334245181/2500000000 : ℝ)*X 1 0+(-1446207339/10000000000 : ℝ)*X 1 1+(508083547/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1749_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2668490341/5000000000 : ℝ)*X 2 0+(5080835501/10000000000 : ℝ)*X 2 1+(-723103677/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1749_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((402296139/1000000000 : ℝ)*X 0 0+(3371548559/10000000000 : ℝ)*X 0 1+(4737767761/10000000000 : ℝ)*X 0 2+(402296139/1000000000 : ℝ)*X 1 0+(3371548559/10000000000 : ℝ)*X 1 1+(4737767761/10000000000 : ℝ)*X 1 2+(402296139/1000000000 : ℝ)*X 2 0+(3371548559/10000000000 : ℝ)*X 2 1+(4737767761/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1749_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1228110147/10000000000 : ℝ)*X 0 0+(2543807623/5000000000 : ℝ)*X 0 1+(137286001/250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1749_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((402411603/1000000000 : ℝ)*X 0 0+(2357791613/5000000000 : ℝ)*X 0 1+(3394198601/10000000000 : ℝ)*X 0 2+(402411603/1000000000 : ℝ)*X 1 0+(2357791613/5000000000 : ℝ)*X 1 1+(3394198601/10000000000 : ℝ)*X 1 2+(402411603/1000000000 : ℝ)*X 2 0+(2357791613/5000000000 : ℝ)*X 2 1+(3394198601/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1749_s4_5 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (359057321312894631315212397/140125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (173390517/50000000000000 : ℝ)*(base19) + (3810353/1250000000000 : ℝ)*(base23) + (2466173/20000000000000 : ℝ)*(lower2) + (8426027/12500000000000 : ℝ)*(upper3) + (10218523/25000000000000 : ℝ)*(upper5) + (195438177596227/12500000000000 : ℝ)*(major0) + (195438177596227/12500000000000 : ℝ)*(major1) + (195438177596227/12500000000000 : ℝ)*(major2) + (598764937055269/25000000000000 : ℝ)*(sp0) + (598765452325871/25000000000000 : ℝ)*(sp1) + (2395061851256277/100000000000000 : ℝ)*(sp2) + (22873365833811/3125000000000 : ℝ)*(sp3) + (2407863441/100000000000000 : ℝ)*(sp4) + (893359581/100000000000000 : ℝ)*(sp5) + (365974300020767/50000000000000 : ℝ)*(f.failure) + (2395062156084517/100000000000000 : ℝ)*(f.sum) + (76855763853/44840000000000000000000000 : ℝ)*base66 + (2296472764603018067/280250000000000000000000000000000 : ℝ)*base67 + (335379599699768067/280250000000000000000000000000000 : ℝ)*base69 + (381945730913518067/280250000000000000000000000000000 : ℝ)*base71 + (1518508244247/280250000000000000000000000 : ℝ)*base73 + (634727305451768067/280250000000000000000000000000000 : ℝ)*base75 + (436258601849018067/280250000000000000000000000000000 : ℝ)*base77 + (571107159382268067/280250000000000000000000000000000 : ℝ)*base79 + (1439366611849/1121000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (2635953/1250000000000000000000 : ℝ)*base89 + (2635953/1250000000000000000000 : ℝ)*base91 + (2635953/1250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(upper0) + hcertificate_margin
theorem rectangle_w1749_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5743/1024 : ℝ) ≤ p) (hpb : p ≤ (5759/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (53402159/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3599/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9027/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2257/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3599/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1749_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1749_box_0 (p : ℝ) (hpa : (5743/1024 : ℝ) ≤ p) (hpb : p ≤ (5759/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-839390963/10000000000 : ℝ)*x 0 + (5426388623/10000000000 : ℝ)*x 1 + (2713194053/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (839390963/10000000000 : ℝ)^5759 ≤ (2456002407639/50000000000000 : ℝ)^4735 := by
    have hnat : (839390963 : ℕ)^5759*50000000000000^4735 ≤ 2456002407639^4735*10000000000^5759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      839390963 10000000000 2456002407639 50000000000000 5759 4735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5426388623/10000000000 : ℝ)^5759 ≤ (4754400033673/10000000000000 : ℝ)^4735 := by
    have hnat : (5426388623 : ℕ)^5759*10000000000000^4735 ≤ 4754400033673^4735*10000000000^5759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5426388623 10000000000 4754400033673 10000000000000 5759 4735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2713194053/5000000000 : ℝ)^5759 ≤ (47543994827353/100000000000000 : ℝ)^4735 := by
    have hnat : (2713194053 : ℕ)^5759*100000000000000^4735 ≤ 47543994827353^4735*5000000000^5759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2713194053 5000000000 47543994827353 100000000000000 5759 4735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5759/1024 : ℝ)) 5759 4735 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-839390963/10000000000 : ℝ), (5426388623/10000000000 : ℝ), (2713194053/5000000000 : ℝ)] ![(2456002407639/50000000000000 : ℝ), (4754400033673/10000000000000 : ℝ), (47543994827353/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-839390963/10000000000 : ℝ)|^5759 ≤ (2456002407639/50000000000000 : ℝ)^4735
        have hw : |(-839390963/10000000000 : ℝ)|=(839390963/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5426388623/10000000000 : ℝ)|^5759 ≤ (4754400033673/10000000000000 : ℝ)^4735
        have hw : |(5426388623/10000000000 : ℝ)|=(5426388623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2713194053/5000000000 : ℝ)|^5759 ≤ (47543994827353/100000000000000 : ℝ)^4735
        have hw : |(2713194053/5000000000 : ℝ)|=(2713194053/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1749_box_1 (p : ℝ) (hpa : (5743/1024 : ℝ) ≤ p) (hpb : p ≤ (5759/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2597253537/5000000000 : ℝ)*x 0 + (-585981053/5000000000 : ℝ)*x 1 + (5426388219/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2597253537/5000000000 : ℝ)^5759 ≤ (45084517563841/100000000000000 : ℝ)^4735 := by
    have hnat : (2597253537 : ℕ)^5759*100000000000000^4735 ≤ 45084517563841^4735*5000000000^5759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2597253537 5000000000 45084517563841 100000000000000 5759 4735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (585981053/5000000000 : ℝ)^5759 ≤ (737148638889/10000000000000 : ℝ)^4735 := by
    have hnat : (585981053 : ℕ)^5759*10000000000000^4735 ≤ 737148638889^4735*5000000000^5759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      585981053 5000000000 737148638889 10000000000000 5759 4735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5426388219/10000000000 : ℝ)^5759 ≤ (47543996031531/100000000000000 : ℝ)^4735 := by
    have hnat : (5426388219 : ℕ)^5759*100000000000000^4735 ≤ 47543996031531^4735*10000000000^5759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5426388219 10000000000 47543996031531 100000000000000 5759 4735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5759/1024 : ℝ)) 5759 4735 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2597253537/5000000000 : ℝ), (-585981053/5000000000 : ℝ), (5426388219/10000000000 : ℝ)] ![(45084517563841/100000000000000 : ℝ), (737148638889/10000000000000 : ℝ), (47543996031531/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2597253537/5000000000 : ℝ)|^5759 ≤ (45084517563841/100000000000000 : ℝ)^4735
        have hw : |(2597253537/5000000000 : ℝ)|=(2597253537/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-585981053/5000000000 : ℝ)|^5759 ≤ (737148638889/10000000000000 : ℝ)^4735
        have hw : |(-585981053/5000000000 : ℝ)|=(585981053/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5426388219/10000000000 : ℝ)|^5759 ≤ (47543996031531/100000000000000 : ℝ)^4735
        have hw : |(5426388219/10000000000 : ℝ)|=(5426388219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1749_box_2 (p : ℝ) (hpa : (5743/1024 : ℝ) ≤ p) (hpb : p ≤ (5759/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (259725357/500000000 : ℝ)*x 0 + (2713194123/5000000000 : ℝ)*x 1 + (-1171961977/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (259725357/500000000 : ℝ)^5759 ≤ (22542259130277/50000000000000 : ℝ)^4735 := by
    have hnat : (259725357 : ℕ)^5759*50000000000000^4735 ≤ 22542259130277^4735*500000000^5759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      259725357 500000000 22542259130277 50000000000000 5759 4735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2713194123/5000000000 : ℝ)^5759 ≤ (23771998159627/50000000000000 : ℝ)^4735 := by
    have hnat : (2713194123 : ℕ)^5759*50000000000000^4735 ≤ 23771998159627^4735*5000000000^5759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2713194123 5000000000 23771998159627 50000000000000 5759 4735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1171961977/10000000000 : ℝ)^5759 ≤ (921435675253/12500000000000 : ℝ)^4735 := by
    have hnat : (1171961977 : ℕ)^5759*12500000000000^4735 ≤ 921435675253^4735*10000000000^5759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1171961977 10000000000 921435675253 12500000000000 5759 4735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5759/1024 : ℝ)) 5759 4735 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(259725357/500000000 : ℝ), (2713194123/5000000000 : ℝ), (-1171961977/10000000000 : ℝ)] ![(22542259130277/50000000000000 : ℝ), (23771998159627/50000000000000 : ℝ), (921435675253/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(259725357/500000000 : ℝ)|^5759 ≤ (22542259130277/50000000000000 : ℝ)^4735
        have hw : |(259725357/500000000 : ℝ)|=(259725357/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2713194123/5000000000 : ℝ)|^5759 ≤ (23771998159627/50000000000000 : ℝ)^4735
        have hw : |(2713194123/5000000000 : ℝ)|=(2713194123/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1171961977/10000000000 : ℝ)|^5759 ≤ (921435675253/12500000000000 : ℝ)^4735
        have hw : |(-1171961977/10000000000 : ℝ)|=(1171961977/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1749_box_3 (p : ℝ) (hpa : (5743/1024 : ℝ) ≤ p) (hpb : p ≤ (5759/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4549502531/10000000000 : ℝ)*x 0 + (474868409/1250000000 : ℝ)*x 1 + (759789483/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4549502531/10000000000 : ℝ)^5759 ≤ (38370242457227/100000000000000 : ℝ)^4735 := by
    have hnat : (4549502531 : ℕ)^5759*100000000000000^4735 ≤ 38370242457227^4735*10000000000^5759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4549502531 10000000000 38370242457227 100000000000000 5759 4735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (474868409/1250000000 : ℝ)^5759 ≤ (15407439031287/50000000000000 : ℝ)^4735 := by
    have hnat : (474868409 : ℕ)^5759*50000000000000^4735 ≤ 15407439031287^4735*1250000000^5759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      474868409 1250000000 15407439031287 50000000000000 5759 4735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (759789483/2000000000 : ℝ)^5759 ≤ (30814879473357/100000000000000 : ℝ)^4735 := by
    have hnat : (759789483 : ℕ)^5759*100000000000000^4735 ≤ 30814879473357^4735*2000000000^5759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      759789483 2000000000 30814879473357 100000000000000 5759 4735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5759/1024 : ℝ)) 5759 4735 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4549502531/10000000000 : ℝ), (474868409/1250000000 : ℝ), (759789483/2000000000 : ℝ)] ![(38370242457227/100000000000000 : ℝ), (15407439031287/50000000000000 : ℝ), (30814879473357/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4549502531/10000000000 : ℝ)|^5759 ≤ (38370242457227/100000000000000 : ℝ)^4735
        have hw : |(4549502531/10000000000 : ℝ)|=(4549502531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(474868409/1250000000 : ℝ)|^5759 ≤ (15407439031287/50000000000000 : ℝ)^4735
        have hw : |(474868409/1250000000 : ℝ)|=(474868409/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(759789483/2000000000 : ℝ)|^5759 ≤ (30814879473357/100000000000000 : ℝ)^4735
        have hw : |(759789483/2000000000 : ℝ)|=(759789483/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1749_box_4 (p : ℝ) (hpa : (5743/1024 : ℝ) ≤ p) (hpb : p ≤ (5759/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-827968589/5000000000 : ℝ)*x 0 + (1282107021/2500000000 : ℝ)*x 1 + (641053517/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (827968589/5000000000 : ℝ)^5759 ≤ (2244826647011/20000000000000 : ℝ)^4735 := by
    have hnat : (827968589 : ℕ)^5759*20000000000000^4735 ≤ 2244826647011^4735*5000000000^5759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      827968589 5000000000 2244826647011 20000000000000 5759 4735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1282107021/2500000000 : ℝ)^5759 ≤ (4438793310333/10000000000000 : ℝ)^4735 := by
    have hnat : (1282107021 : ℕ)^5759*10000000000000^4735 ≤ 4438793310333^4735*2500000000^5759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1282107021 2500000000 4438793310333 10000000000000 5759 4735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (641053517/1250000000 : ℝ)^5759 ≤ (22193966825369/50000000000000 : ℝ)^4735 := by
    have hnat : (641053517 : ℕ)^5759*50000000000000^4735 ≤ 22193966825369^4735*1250000000^5759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      641053517 1250000000 22193966825369 50000000000000 5759 4735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5759/1024 : ℝ)) 5759 4735 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-827968589/5000000000 : ℝ), (1282107021/2500000000 : ℝ), (641053517/1250000000 : ℝ)] ![(2244826647011/20000000000000 : ℝ), (4438793310333/10000000000000 : ℝ), (22193966825369/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-827968589/5000000000 : ℝ)|^5759 ≤ (2244826647011/20000000000000 : ℝ)^4735
        have hw : |(-827968589/5000000000 : ℝ)|=(827968589/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1282107021/2500000000 : ℝ)|^5759 ≤ (4438793310333/10000000000000 : ℝ)^4735
        have hw : |(1282107021/2500000000 : ℝ)|=(1282107021/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(641053517/1250000000 : ℝ)|^5759 ≤ (22193966825369/50000000000000 : ℝ)^4735
        have hw : |(641053517/1250000000 : ℝ)|=(641053517/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1749_box_5 (p : ℝ) (hpa : (5743/1024 : ℝ) ≤ p) (hpb : p ≤ (5759/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5394051003/10000000000 : ℝ)*x 0 + (-1306412813/10000000000 : ℝ)*x 1 + (2564214099/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5394051003/10000000000 : ℝ)^5759 ≤ (47199619010621/100000000000000 : ℝ)^4735 := by
    have hnat : (5394051003 : ℕ)^5759*100000000000000^4735 ≤ 47199619010621^4735*10000000000^5759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394051003 10000000000 47199619010621 100000000000000 5759 4735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1306412813/10000000000 : ℝ)^5759 ≤ (8412446665443/100000000000000 : ℝ)^4735 := by
    have hnat : (1306412813 : ℕ)^5759*100000000000000^4735 ≤ 8412446665443^4735*10000000000^5759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1306412813 10000000000 8412446665443 100000000000000 5759 4735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2564214099/5000000000 : ℝ)^5759 ≤ (5548491787927/12500000000000 : ℝ)^4735 := by
    have hnat : (2564214099 : ℕ)^5759*12500000000000^4735 ≤ 5548491787927^4735*5000000000^5759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2564214099 5000000000 5548491787927 12500000000000 5759 4735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5759/1024 : ℝ)) 5759 4735 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5394051003/10000000000 : ℝ), (-1306412813/10000000000 : ℝ), (2564214099/5000000000 : ℝ)] ![(47199619010621/100000000000000 : ℝ), (8412446665443/100000000000000 : ℝ), (5548491787927/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5394051003/10000000000 : ℝ)|^5759 ≤ (47199619010621/100000000000000 : ℝ)^4735
        have hw : |(5394051003/10000000000 : ℝ)|=(5394051003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1306412813/10000000000 : ℝ)|^5759 ≤ (8412446665443/100000000000000 : ℝ)^4735
        have hw : |(-1306412813/10000000000 : ℝ)|=(1306412813/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2564214099/5000000000 : ℝ)|^5759 ≤ (5548491787927/12500000000000 : ℝ)^4735
        have hw : |(2564214099/5000000000 : ℝ)|=(2564214099/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1749_box_6 (p : ℝ) (hpa : (5743/1024 : ℝ) ≤ p) (hpb : p ≤ (5759/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1348512769/2500000000 : ℝ)*x 0 + (1282107039/2500000000 : ℝ)*x 1 + (-130641277/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1348512769/2500000000 : ℝ)^5759 ≤ (2949976236721/6250000000000 : ℝ)^4735 := by
    have hnat : (1348512769 : ℕ)^5759*6250000000000^4735 ≤ 2949976236721^4735*2500000000^5759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348512769 2500000000 2949976236721 6250000000000 5759 4735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1282107039/2500000000 : ℝ)^5759 ≤ (44387933861279/100000000000000 : ℝ)^4735 := by
    have hnat : (1282107039 : ℕ)^5759*100000000000000^4735 ≤ 44387933861279^4735*2500000000^5759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1282107039 2500000000 44387933861279 100000000000000 5759 4735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (130641277/1000000000 : ℝ)^5759 ≤ (841244632867/10000000000000 : ℝ)^4735 := by
    have hnat : (130641277 : ℕ)^5759*10000000000000^4735 ≤ 841244632867^4735*1000000000^5759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      130641277 1000000000 841244632867 10000000000000 5759 4735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5759/1024 : ℝ)) 5759 4735 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1348512769/2500000000 : ℝ), (1282107039/2500000000 : ℝ), (-130641277/1000000000 : ℝ)] ![(2949976236721/6250000000000 : ℝ), (44387933861279/100000000000000 : ℝ), (841244632867/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1348512769/2500000000 : ℝ)|^5759 ≤ (2949976236721/6250000000000 : ℝ)^4735
        have hw : |(1348512769/2500000000 : ℝ)|=(1348512769/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1282107039/2500000000 : ℝ)|^5759 ≤ (44387933861279/100000000000000 : ℝ)^4735
        have hw : |(1282107039/2500000000 : ℝ)|=(1282107039/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-130641277/1000000000 : ℝ)|^5759 ≤ (841244632867/10000000000000 : ℝ)^4735
        have hw : |(-130641277/1000000000 : ℝ)|=(130641277/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1749_box_7 (p : ℝ) (hpa : (5743/1024 : ℝ) ≤ p) (hpb : p ≤ (5759/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1729984807/5000000000 : ℝ)*x 0 + (542698497/1250000000 : ℝ)*x 1 + (4341588109/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1729984807/5000000000 : ℝ)^5759 ≤ (27503704335123/100000000000000 : ℝ)^4735 := by
    have hnat : (1729984807 : ℕ)^5759*100000000000000^4735 ≤ 27503704335123^4735*5000000000^5759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1729984807 5000000000 27503704335123 100000000000000 5759 4735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (542698497/1250000000 : ℝ)^5759 ≤ (566377299223/1562500000000 : ℝ)^4735 := by
    have hnat : (542698497 : ℕ)^5759*1562500000000^4735 ≤ 566377299223^4735*1250000000^5759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      542698497 1250000000 566377299223 1562500000000 5759 4735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4341588109/10000000000 : ℝ)^5759 ≤ (36248148500839/100000000000000 : ℝ)^4735 := by
    have hnat : (4341588109 : ℕ)^5759*100000000000000^4735 ≤ 36248148500839^4735*10000000000^5759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4341588109 10000000000 36248148500839 100000000000000 5759 4735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5759/1024 : ℝ)) 5759 4735 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1729984807/5000000000 : ℝ), (542698497/1250000000 : ℝ), (4341588109/10000000000 : ℝ)] ![(27503704335123/100000000000000 : ℝ), (566377299223/1562500000000 : ℝ), (36248148500839/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1729984807/5000000000 : ℝ)|^5759 ≤ (27503704335123/100000000000000 : ℝ)^4735
        have hw : |(1729984807/5000000000 : ℝ)|=(1729984807/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(542698497/1250000000 : ℝ)|^5759 ≤ (566377299223/1562500000000 : ℝ)^4735
        have hw : |(542698497/1250000000 : ℝ)|=(542698497/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4341588109/10000000000 : ℝ)|^5759 ≤ (36248148500839/100000000000000 : ℝ)^4735
        have hw : |(4341588109/10000000000 : ℝ)|=(4341588109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1749_box_8 (p : ℝ) (hpa : (5743/1024 : ℝ) ≤ p) (hpb : p ≤ (5759/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1478387233/10000000000 : ℝ)*x 0 + (4901659489/10000000000 : ℝ)*x 1 + (343049609/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1478387233/10000000000 : ℝ)^5759 ≤ (9777887582423/100000000000000 : ℝ)^4735 := by
    have hnat : (1478387233 : ℕ)^5759*100000000000000^4735 ≤ 9777887582423^4735*10000000000^5759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1478387233 10000000000 9777887582423 100000000000000 5759 4735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4901659489/10000000000 : ℝ)^5759 ≤ (10503067869927/25000000000000 : ℝ)^4735 := by
    have hnat : (4901659489 : ℕ)^5759*25000000000000^4735 ≤ 10503067869927^4735*10000000000^5759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4901659489 10000000000 10503067869927 25000000000000 5759 4735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (343049609/625000000 : ℝ)^5759 ≤ (24104920462861/50000000000000 : ℝ)^4735 := by
    have hnat : (343049609 : ℕ)^5759*50000000000000^4735 ≤ 24104920462861^4735*625000000^5759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      343049609 625000000 24104920462861 50000000000000 5759 4735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5759/1024 : ℝ)) 5759 4735 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1478387233/10000000000 : ℝ), (4901659489/10000000000 : ℝ), (343049609/625000000 : ℝ)] ![(9777887582423/100000000000000 : ℝ), (10503067869927/25000000000000 : ℝ), (24104920462861/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1478387233/10000000000 : ℝ)|^5759 ≤ (9777887582423/100000000000000 : ℝ)^4735
        have hw : |(-1478387233/10000000000 : ℝ)|=(1478387233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4901659489/10000000000 : ℝ)|^5759 ≤ (10503067869927/25000000000000 : ℝ)^4735
        have hw : |(4901659489/10000000000 : ℝ)|=(4901659489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(343049609/625000000 : ℝ)|^5759 ≤ (24104920462861/50000000000000 : ℝ)^4735
        have hw : |(343049609/625000000 : ℝ)|=(343049609/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1749_box_9 (p : ℝ) (hpa : (5743/1024 : ℝ) ≤ p) (hpb : p ≤ (5759/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2576389111/5000000000 : ℝ)*x 0 + (-1142370807/10000000000 : ℝ)*x 1 + (1097759261/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2576389111/5000000000 : ℝ)^5759 ≤ (44644400294007/100000000000000 : ℝ)^4735 := by
    have hnat : (2576389111 : ℕ)^5759*100000000000000^4735 ≤ 44644400294007^4735*5000000000^5759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2576389111 5000000000 44644400294007 100000000000000 5759 4735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1142370807/10000000000 : ℝ)^5759 ≤ (893216425891/12500000000000 : ℝ)^4735 := by
    have hnat : (1142370807 : ℕ)^5759*12500000000000^4735 ≤ 893216425891^4735*10000000000^5759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1142370807 10000000000 893216425891 12500000000000 5759 4735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1097759261/2000000000 : ℝ)^5759 ≤ (6026233535553/12500000000000 : ℝ)^4735 := by
    have hnat : (1097759261 : ℕ)^5759*12500000000000^4735 ≤ 6026233535553^4735*2000000000^5759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1097759261 2000000000 6026233535553 12500000000000 5759 4735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5759/1024 : ℝ)) 5759 4735 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2576389111/5000000000 : ℝ), (-1142370807/10000000000 : ℝ), (1097759261/2000000000 : ℝ)] ![(44644400294007/100000000000000 : ℝ), (893216425891/12500000000000 : ℝ), (6026233535553/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2576389111/5000000000 : ℝ)|^5759 ≤ (44644400294007/100000000000000 : ℝ)^4735
        have hw : |(2576389111/5000000000 : ℝ)|=(2576389111/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1142370807/10000000000 : ℝ)|^5759 ≤ (893216425891/12500000000000 : ℝ)^4735
        have hw : |(-1142370807/10000000000 : ℝ)|=(1142370807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1097759261/2000000000 : ℝ)|^5759 ≤ (6026233535553/12500000000000 : ℝ)^4735
        have hw : |(1097759261/2000000000 : ℝ)|=(1097759261/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1749_box_10 (p : ℝ) (hpa : (5743/1024 : ℝ) ≤ p) (hpb : p ≤ (5759/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5152779071/10000000000 : ℝ)*x 0 + (42881217/78125000 : ℝ)*x 1 + (-9138963/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5152779071/10000000000 : ℝ)^5759 ≤ (8928881848131/20000000000000 : ℝ)^4735 := by
    have hnat : (5152779071 : ℕ)^5759*20000000000000^4735 ≤ 8928881848131^4735*10000000000^5759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5152779071 10000000000 8928881848131 20000000000000 5759 4735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (42881217/78125000 : ℝ)^5759 ≤ (12052465658303/25000000000000 : ℝ)^4735 := by
    have hnat : (42881217 : ℕ)^5759*25000000000000^4735 ≤ 12052465658303^4735*78125000^5759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42881217 78125000 12052465658303 25000000000000 5759 4735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (9138963/80000000 : ℝ)^5759 ≤ (7145728120501/100000000000000 : ℝ)^4735 := by
    have hnat : (9138963 : ℕ)^5759*100000000000000^4735 ≤ 7145728120501^4735*80000000^5759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9138963 80000000 7145728120501 100000000000000 5759 4735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5759/1024 : ℝ)) 5759 4735 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5152779071/10000000000 : ℝ), (42881217/78125000 : ℝ), (-9138963/80000000 : ℝ)] ![(8928881848131/20000000000000 : ℝ), (12052465658303/25000000000000 : ℝ), (7145728120501/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5152779071/10000000000 : ℝ)|^5759 ≤ (8928881848131/20000000000000 : ℝ)^4735
        have hw : |(5152779071/10000000000 : ℝ)|=(5152779071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(42881217/78125000 : ℝ)|^5759 ≤ (12052465658303/25000000000000 : ℝ)^4735
        have hw : |(42881217/78125000 : ℝ)|=(42881217/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-9138963/80000000 : ℝ)|^5759 ≤ (7145728120501/100000000000000 : ℝ)^4735
        have hw : |(-9138963/80000000 : ℝ)|=(9138963/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1749_box_11 (p : ℝ) (hpa : (5743/1024 : ℝ) ≤ p) (hpb : p ≤ (5759/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4767106657/10000000000 : ℝ)*x 0 + (3684868201/10000000000 : ℝ)*x 1 + (736973527/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4767106657/10000000000 : ℝ)^5759 ≤ (2538362710757/6250000000000 : ℝ)^4735 := by
    have hnat : (4767106657 : ℕ)^5759*6250000000000^4735 ≤ 2538362710757^4735*10000000000^5759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4767106657 10000000000 2538362710757 6250000000000 5759 4735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3684868201/10000000000 : ℝ)^5759 ≤ (3711637634497/12500000000000 : ℝ)^4735 := by
    have hnat : (3684868201 : ℕ)^5759*12500000000000^4735 ≤ 3711637634497^4735*10000000000^5759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3684868201 10000000000 3711637634497 12500000000000 5759 4735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (736973527/2000000000 : ℝ)^5759 ≤ (29693095528733/100000000000000 : ℝ)^4735 := by
    have hnat : (736973527 : ℕ)^5759*100000000000000^4735 ≤ 29693095528733^4735*2000000000^5759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      736973527 2000000000 29693095528733 100000000000000 5759 4735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5759/1024 : ℝ)) 5759 4735 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4767106657/10000000000 : ℝ), (3684868201/10000000000 : ℝ), (736973527/2000000000 : ℝ)] ![(2538362710757/6250000000000 : ℝ), (3711637634497/12500000000000 : ℝ), (29693095528733/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4767106657/10000000000 : ℝ)|^5759 ≤ (2538362710757/6250000000000 : ℝ)^4735
        have hw : |(4767106657/10000000000 : ℝ)|=(4767106657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3684868201/10000000000 : ℝ)|^5759 ≤ (3711637634497/12500000000000 : ℝ)^4735
        have hw : |(3684868201/10000000000 : ℝ)|=(3684868201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(736973527/2000000000 : ℝ)|^5759 ≤ (29693095528733/100000000000000 : ℝ)^4735
        have hw : |(736973527/2000000000 : ℝ)|=(736973527/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1749_box_12 (p : ℝ) (hpa : (5743/1024 : ℝ) ≤ p) (hpb : p ≤ (5759/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1003287109/10000000000 : ℝ)*x 0 + (5639774039/10000000000 : ℝ)*x 1 + (637281973/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1003287109/10000000000 : ℝ)^5759 ≤ (1525497796161/25000000000000 : ℝ)^4735 := by
    have hnat : (1003287109 : ℕ)^5759*25000000000000^4735 ≤ 1525497796161^4735*10000000000^5759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1003287109 10000000000 1525497796161 25000000000000 5759 4735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5639774039/10000000000 : ℝ)^5759 ≤ (24913749703143/50000000000000 : ℝ)^4735 := by
    have hnat : (5639774039 : ℕ)^5759*50000000000000^4735 ≤ 24913749703143^4735*10000000000^5759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5639774039 10000000000 24913749703143 50000000000000 5759 4735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (637281973/1250000000 : ℝ)^5759 ≤ (22035254695759/50000000000000 : ℝ)^4735 := by
    have hnat : (637281973 : ℕ)^5759*50000000000000^4735 ≤ 22035254695759^4735*1250000000^5759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      637281973 1250000000 22035254695759 50000000000000 5759 4735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5759/1024 : ℝ)) 5759 4735 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1003287109/10000000000 : ℝ), (5639774039/10000000000 : ℝ), (637281973/1250000000 : ℝ)] ![(1525497796161/25000000000000 : ℝ), (24913749703143/50000000000000 : ℝ), (22035254695759/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1003287109/10000000000 : ℝ)|^5759 ≤ (1525497796161/25000000000000 : ℝ)^4735
        have hw : |(-1003287109/10000000000 : ℝ)|=(1003287109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5639774039/10000000000 : ℝ)|^5759 ≤ (24913749703143/50000000000000 : ℝ)^4735
        have hw : |(5639774039/10000000000 : ℝ)|=(5639774039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(637281973/1250000000 : ℝ)|^5759 ≤ (22035254695759/50000000000000 : ℝ)^4735
        have hw : |(637281973/1250000000 : ℝ)|=(637281973/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1749_box_13 (p : ℝ) (hpa : (5743/1024 : ℝ) ≤ p) (hpb : p ≤ (5759/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2707164847/5000000000 : ℝ)*x 0 + (-1319360027/10000000000 : ℝ)*x 1 + (5098256523/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2707164847/5000000000 : ℝ)^5759 ≤ (23707763023197/50000000000000 : ℝ)^4735 := by
    have hnat : (2707164847 : ℕ)^5759*50000000000000^4735 ≤ 23707763023197^4735*5000000000^5759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2707164847 5000000000 23707763023197 50000000000000 5759 4735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1319360027/10000000000 : ℝ)^5759 ≤ (8513956768963/100000000000000 : ℝ)^4735 := by
    have hnat : (1319360027 : ℕ)^5759*100000000000000^4735 ≤ 8513956768963^4735*10000000000^5759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1319360027 10000000000 8513956768963 100000000000000 5759 4735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5098256523/10000000000 : ℝ)^5759 ≤ (22035258580553/50000000000000 : ℝ)^4735 := by
    have hnat : (5098256523 : ℕ)^5759*50000000000000^4735 ≤ 22035258580553^4735*10000000000^5759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5098256523 10000000000 22035258580553 50000000000000 5759 4735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5759/1024 : ℝ)) 5759 4735 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2707164847/5000000000 : ℝ), (-1319360027/10000000000 : ℝ), (5098256523/10000000000 : ℝ)] ![(23707763023197/50000000000000 : ℝ), (8513956768963/100000000000000 : ℝ), (22035258580553/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2707164847/5000000000 : ℝ)|^5759 ≤ (23707763023197/50000000000000 : ℝ)^4735
        have hw : |(2707164847/5000000000 : ℝ)|=(2707164847/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1319360027/10000000000 : ℝ)|^5759 ≤ (8513956768963/100000000000000 : ℝ)^4735
        have hw : |(-1319360027/10000000000 : ℝ)|=(1319360027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5098256523/10000000000 : ℝ)|^5759 ≤ (22035258580553/50000000000000 : ℝ)^4735
        have hw : |(5098256523/10000000000 : ℝ)|=(5098256523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1749_box_14 (p : ℝ) (hpa : (5743/1024 : ℝ) ≤ p) (hpb : p ≤ (5759/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1082865941/2000000000 : ℝ)*x 0 + (15932051/31250000 : ℝ)*x 1 + (-263872057/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1082865941/2000000000 : ℝ)^5759 ≤ (47415526163559/100000000000000 : ℝ)^4735 := by
    have hnat : (1082865941 : ℕ)^5759*100000000000000^4735 ≤ 47415526163559^4735*2000000000^5759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082865941 2000000000 47415526163559 100000000000000 5759 4735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (15932051/31250000 : ℝ)^5759 ≤ (8814103005367/20000000000000 : ℝ)^4735 := by
    have hnat : (15932051 : ℕ)^5759*20000000000000^4735 ≤ 8814103005367^4735*31250000^5759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      15932051 31250000 8814103005367 20000000000000 5759 4735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (263872057/2000000000 : ℝ)^5759 ≤ (2128489698479/25000000000000 : ℝ)^4735 := by
    have hnat : (263872057 : ℕ)^5759*25000000000000^4735 ≤ 2128489698479^4735*2000000000^5759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263872057 2000000000 2128489698479 25000000000000 5759 4735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5759/1024 : ℝ)) 5759 4735 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1082865941/2000000000 : ℝ), (15932051/31250000 : ℝ), (-263872057/2000000000 : ℝ)] ![(47415526163559/100000000000000 : ℝ), (8814103005367/20000000000000 : ℝ), (2128489698479/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1082865941/2000000000 : ℝ)|^5759 ≤ (47415526163559/100000000000000 : ℝ)^4735
        have hw : |(1082865941/2000000000 : ℝ)|=(1082865941/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(15932051/31250000 : ℝ)|^5759 ≤ (8814103005367/20000000000000 : ℝ)^4735
        have hw : |(15932051/31250000 : ℝ)|=(15932051/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-263872057/2000000000 : ℝ)|^5759 ≤ (2128489698479/25000000000000 : ℝ)^4735
        have hw : |(-263872057/2000000000 : ℝ)|=(263872057/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1749_box_15 (p : ℝ) (hpa : (5743/1024 : ℝ) ≤ p) (hpb : p ≤ (5759/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (668886647/2000000000 : ℝ)*x 0 + (4396315209/10000000000 : ℝ)*x 1 + (4396313441/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668886647/2000000000 : ℝ)^5759 ≤ (13195371787723/50000000000000 : ℝ)^4735 := by
    have hnat : (668886647 : ℕ)^5759*50000000000000^4735 ≤ 13195371787723^4735*2000000000^5759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668886647 2000000000 13195371787723 50000000000000 5759 4735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4396315209/10000000000 : ℝ)^5759 ≤ (18402318603719/50000000000000 : ℝ)^4735 := by
    have hnat : (4396315209 : ℕ)^5759*50000000000000^4735 ≤ 18402318603719^4735*10000000000^5759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4396315209 10000000000 18402318603719 50000000000000 5759 4735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4396313441/10000000000 : ℝ)^5759 ≤ (36804619205343/100000000000000 : ℝ)^4735 := by
    have hnat : (4396313441 : ℕ)^5759*100000000000000^4735 ≤ 36804619205343^4735*10000000000^5759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4396313441 10000000000 36804619205343 100000000000000 5759 4735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5759/1024 : ℝ)) 5759 4735 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668886647/2000000000 : ℝ), (4396315209/10000000000 : ℝ), (4396313441/10000000000 : ℝ)] ![(13195371787723/50000000000000 : ℝ), (18402318603719/50000000000000 : ℝ), (36804619205343/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668886647/2000000000 : ℝ)|^5759 ≤ (13195371787723/50000000000000 : ℝ)^4735
        have hw : |(668886647/2000000000 : ℝ)|=(668886647/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4396315209/10000000000 : ℝ)|^5759 ≤ (18402318603719/50000000000000 : ℝ)^4735
        have hw : |(4396315209/10000000000 : ℝ)|=(4396315209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4396313441/10000000000 : ℝ)|^5759 ≤ (36804619205343/100000000000000 : ℝ)^4735
        have hw : |(4396313441/10000000000 : ℝ)|=(4396313441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1749_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (5743/1024 : ℝ) ≤ p) (hpb : p ≤ (5759/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (53402159/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3599/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2257/25000 : ℝ)*pair X i i ≤ pair X i h) :
    -(34447/50000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(29031/50000 : ℝ) ∧ (20377/25000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (92881/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3599/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2257/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3599/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2257/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3599/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2257/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3599/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2257/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3599/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2257/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3599/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2257/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2257/25000 : ℝ) ^ (5743/1024 : ℝ) ≤ (138848529035091/100000000000000000000 : ℝ) := by
    have hpowers : (2257/25000 : ℝ)^5743 ≤ (138848529035091/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2257 : ℕ)^5743*100000000000000000000^1024 ≤ 138848529035091^1024*25000^5743 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2257 25000 138848529035091 100000000000000000000 5743 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2257/25000 : ℝ)) (X := (138848529035091/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5743 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3599/20000 : ℝ) ^ (5743/1024 : ℝ) ≤ (3323263741793973/50000000000000000000 : ℝ) := by
    have hpowers : (3599/20000 : ℝ)^5743 ≤ (3323263741793973/50000000000000000000 : ℝ)^1024 := by
      have hnat : (3599 : ℕ)^5743*50000000000000000000^1024 ≤ 3323263741793973^1024*20000^5743 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3599 20000 3323263741793973 50000000000000000000 5743 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3599/20000 : ℝ)) (X := (3323263741793973/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5743 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000138848529035091/50000000000000000000 : ℝ) ≤ (5000002475722297/5000000000000000 : ℝ) ^ (5743/1024 : ℝ) := by
    have hpowers : (50000138848529035091/50000000000000000000 : ℝ)^1024 ≤ (5000002475722297/5000000000000000 : ℝ)^5743 := by
      have hnat : (50000138848529035091 : ℕ)^1024*5000000000000000^5743 ≤ 5000002475722297^5743*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000138848529035091 50000000000000000000 5000002475722297 5000000000000000 1024 5743 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000002475722297/5000000000000000 : ℝ)) (X := (50000138848529035091/50000000000000000000 : ℝ)) (by norm_num) 5743 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100006785376012623037/100000000000000000000 : ℝ) ≤ (5000060491305461/5000000000000000 : ℝ) ^ (5743/1024 : ℝ) := by
    have hpowers : (100006785376012623037/100000000000000000000 : ℝ)^1024 ≤ (5000060491305461/5000000000000000 : ℝ)^5743 := by
      have hnat : (100006785376012623037 : ℕ)^1024*5000000000000000^5743 ≤ 5000060491305461^5743*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100006785376012623037 100000000000000000000 5000060491305461 5000000000000000 1024 5743 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000060491305461/5000000000000000 : ℝ)) (X := (100006785376012623037/100000000000000000000 : ℝ)) (by norm_num) 5743 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25003323263741793973/25000000000000000000 : ℝ) ≤ (40000948055109/40000000000000 : ℝ) ^ (5743/1024 : ℝ) := by
    have hpowers : (25003323263741793973/25000000000000000000 : ℝ)^1024 ≤ (40000948055109/40000000000000 : ℝ)^5743 := by
      have hnat : (25003323263741793973 : ℕ)^1024*40000000000000^5743 ≤ 40000948055109^5743*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25003323263741793973 25000000000000000000 40000948055109 40000000000000 1024 5743 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (40000948055109/40000000000000 : ℝ)) (X := (25003323263741793973/25000000000000000000 : ℝ)) (by norm_num) 5743 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(138848529035091/100000000000000000000 : ℝ) ≤ ((20999519751958889/21000000000000000 : ℝ)+2*(2071985113/16012500000000 : ℝ)*(2257/25000 : ℝ))^(5743/1024 : ℝ) := by
    rw [show (20999519751958889/21000000000000000 : ℝ)+2*(2071985113/16012500000000 : ℝ)*(2257/25000 : ℝ)=(5000002475722297/5000000000000000 : ℝ) by norm_num, show 1+2*(138848529035091/100000000000000000000 : ℝ)=(50000138848529035091/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3323263741793973/50000000000000000000 : ℝ)+(138848529035091/100000000000000000000 : ℝ) ≤ ((20999519751958889/21000000000000000 : ℝ)+(2071985113/16012500000000 : ℝ)*((3599/20000 : ℝ)+(2257/25000 : ℝ)))^(5743/1024 : ℝ) := by
    rw [show (20999519751958889/21000000000000000 : ℝ)+(2071985113/16012500000000 : ℝ)*((3599/20000 : ℝ)+(2257/25000 : ℝ))=(5000060491305461/5000000000000000 : ℝ) by norm_num, show 1+(3323263741793973/50000000000000000000 : ℝ)+(138848529035091/100000000000000000000 : ℝ)=(100006785376012623037/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3323263741793973/50000000000000000000 : ℝ) ≤ ((20999519751958889/21000000000000000 : ℝ)+2*(2071985113/16012500000000 : ℝ)*(3599/20000 : ℝ))^(5743/1024 : ℝ) := by
    rw [show (20999519751958889/21000000000000000 : ℝ)+2*(2071985113/16012500000000 : ℝ)*(3599/20000 : ℝ)=(40000948055109/40000000000000 : ℝ) by norm_num, show 1+2*(3323263741793973/50000000000000000000 : ℝ)=(25003323263741793973/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (20999519751958889/21000000000000000 : ℝ)*(X 1 0+X 2 0)+(2071985113/16012500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5743/1024 : ℝ)) (lo := (2257/25000 : ℝ)) (hi := (3599/20000 : ℝ)) (c := (20999519751958889/21000000000000000 : ℝ)) (alpha := (2071985113/16012500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (20999519751958889/21000000000000000 : ℝ)*(X 0 1+X 2 1)+(2071985113/16012500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5743/1024 : ℝ)) (lo := (2257/25000 : ℝ)) (hi := (3599/20000 : ℝ)) (c := (20999519751958889/21000000000000000 : ℝ)) (alpha := (2071985113/16012500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (20999519751958889/21000000000000000 : ℝ)*(X 0 2+X 1 2)+(2071985113/16012500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5743/1024 : ℝ)) (lo := (2257/25000 : ℝ)) (hi := (3599/20000 : ℝ)) (c := (20999519751958889/21000000000000000 : ℝ)) (alpha := (2071985113/16012500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-839390963/10000000000 : ℝ)*X 0 0+(5426388623/10000000000 : ℝ)*X 0 1+(2713194053/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1749_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2597253537/5000000000 : ℝ)*X 1 0+(-585981053/5000000000 : ℝ)*X 1 1+(5426388219/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1749_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((259725357/500000000 : ℝ)*X 2 0+(2713194123/5000000000 : ℝ)*X 2 1+(-1171961977/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1749_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4549502531/10000000000 : ℝ)*X 0 0+(474868409/1250000000 : ℝ)*X 0 1+(759789483/2000000000 : ℝ)*X 0 2+(4549502531/10000000000 : ℝ)*X 1 0+(474868409/1250000000 : ℝ)*X 1 1+(759789483/2000000000 : ℝ)*X 1 2+(4549502531/10000000000 : ℝ)*X 2 0+(474868409/1250000000 : ℝ)*X 2 1+(759789483/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1749_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-827968589/5000000000 : ℝ)*X 0 0+(1282107021/2500000000 : ℝ)*X 0 1+(641053517/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1749_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5394051003/10000000000 : ℝ)*X 1 0+(-1306412813/10000000000 : ℝ)*X 1 1+(2564214099/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1749_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1348512769/2500000000 : ℝ)*X 2 0+(1282107039/2500000000 : ℝ)*X 2 1+(-130641277/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1749_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1729984807/5000000000 : ℝ)*X 0 0+(542698497/1250000000 : ℝ)*X 0 1+(4341588109/10000000000 : ℝ)*X 0 2+(1729984807/5000000000 : ℝ)*X 1 0+(542698497/1250000000 : ℝ)*X 1 1+(4341588109/10000000000 : ℝ)*X 1 2+(1729984807/5000000000 : ℝ)*X 2 0+(542698497/1250000000 : ℝ)*X 2 1+(4341588109/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1749_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1478387233/10000000000 : ℝ)*X 0 0+(4901659489/10000000000 : ℝ)*X 0 1+(343049609/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1749_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((2576389111/5000000000 : ℝ)*X 1 0+(-1142370807/10000000000 : ℝ)*X 1 1+(1097759261/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1749_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5152779071/10000000000 : ℝ)*X 2 0+(42881217/78125000 : ℝ)*X 2 1+(-9138963/80000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1749_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4767106657/10000000000 : ℝ)*X 0 0+(3684868201/10000000000 : ℝ)*X 0 1+(736973527/2000000000 : ℝ)*X 0 2+(4767106657/10000000000 : ℝ)*X 1 0+(3684868201/10000000000 : ℝ)*X 1 1+(736973527/2000000000 : ℝ)*X 1 2+(4767106657/10000000000 : ℝ)*X 2 0+(3684868201/10000000000 : ℝ)*X 2 1+(736973527/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1749_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1003287109/10000000000 : ℝ)*X 0 0+(5639774039/10000000000 : ℝ)*X 0 1+(637281973/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1749_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((2707164847/5000000000 : ℝ)*X 1 0+(-1319360027/10000000000 : ℝ)*X 1 1+(5098256523/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1749_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((1082865941/2000000000 : ℝ)*X 2 0+(15932051/31250000 : ℝ)*X 2 1+(-263872057/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1749_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((668886647/2000000000 : ℝ)*X 0 0+(4396315209/10000000000 : ℝ)*X 0 1+(4396313441/10000000000 : ℝ)*X 0 2+(668886647/2000000000 : ℝ)*X 1 0+(4396315209/10000000000 : ℝ)*X 1 1+(4396313441/10000000000 : ℝ)*X 1 2+(668886647/2000000000 : ℝ)*X 2 0+(4396315209/10000000000 : ℝ)*X 2 1+(4396313441/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1749_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-34447/50000 : ℝ) ≤ (-241119985673940206429765042129/350000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (5148789/100000000000000 : ℝ)*(upper3) + (5745157/100000000000000 : ℝ)*(upper4) + (22760759/100000000000000 : ℝ)*(upper5) + (1046224359449161/100000000000000 : ℝ)*(major0) + (1046224359449161/100000000000000 : ℝ)*(major1) + (1046224359449161/100000000000000 : ℝ)*(major2) + (282301903/100000000000000 : ℝ)*(sp2) + (106946699/50000000000000 : ℝ)*(sp3) + (40640670027063/2500000000000 : ℝ)*(sp4) + (40640666917291/2500000000000 : ℝ)*(sp5) + (812813317704713/50000000000000 : ℝ)*(sp6) + (97957079090603/20000000000000 : ℝ)*(sp7) + (14578601/12500000000000 : ℝ)*(sp8) + (30127461/12500000000000 : ℝ)*(sp13) + (489785609346413/100000000000000 : ℝ)*(f.failure) + (50800841178479/3125000000000 : ℝ)*(f.sum) + (2998749802669/1601250000000000000000000000 : ℝ)*base66 + (511623586492709869/128100000000000000000000000000000 : ℝ)*base67 + (499016498301809869/128100000000000000000000000000000 : ℝ)*base69 + (299643930411509869/128100000000000000000000000000000 : ℝ)*base71 + (1488633612091/400312500000000000000000000 : ℝ)*base74 + (512091707318609869/128100000000000000000000000000000 : ℝ)*base75 + (179988013240890131/128100000000000000000000000000000 : ℝ)*base78 + (71920566143490131/128100000000000000000000000000000 : ℝ)*base80 + (11982575306587/3202500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (8105667/2500000000000000000000 : ℝ)*base89 + (8105667/2500000000000000000000 : ℝ)*base91 + (8105667/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (29031/50000 : ℝ) ≤ (6198423823355104342684945029669/10675000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2979319/20000000000000 : ℝ)*(upper0) + (227971/4000000000000 : ℝ)*(lower1) + (26660489/100000000000000 : ℝ)*(upper4) + (1169162210214639/100000000000000 : ℝ)*(major0) + (1169162210214639/100000000000000 : ℝ)*(major1) + (1169162210214639/100000000000000 : ℝ)*(major2) + (354325900521277/20000000000000 : ℝ)*(sp0) + (177163084633451/10000000000000 : ℝ)*(sp1) + (35432601924757/2000000000000 : ℝ)*(sp2) + (273669141365959/50000000000000 : ℝ)*(sp3) + (20585113/12500000000000 : ℝ)*(sp5) + (228694391/25000000000000 : ℝ)*(sp6) + (43322823/25000000000000 : ℝ)*(sp7) + (1508409029/100000000000000 : ℝ)*(sp8) + (54733845602321/10000000000000 : ℝ)*(f.failure) + (885815505507707/50000000000000 : ℝ)*(f.sum) + (80939592481/1067500000000000000000000000 : ℝ)*base65 + (329741726741566777/42700000000000000000000000000000 : ℝ)*base67 + (67025985999566777/42700000000000000000000000000000 : ℝ)*base69 + (92037681201766777/42700000000000000000000000000000 : ℝ)*base71 + (6593173460927/533750000000000000000000000 : ℝ)*base74 + (32400671460366777/42700000000000000000000000000000 : ℝ)*base75 + (186121263709366777/42700000000000000000000000000000 : ℝ)*base77 + (398409376608033223/42700000000000000000000000000000 : ℝ)*base80 + (2842611163907/533750000000000000000000000 : ℝ)*base82 + (688961/250000000000000000000 : ℝ)*base90 + (688961/250000000000000000000 : ℝ)*base92 + (688961/250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (20377/25000 : ℝ) ≤ (17830439787054767005290750659/21875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (15749171/25000000000000 : ℝ)*(lower3) + (191721/156250000000 : ℝ)*(upper4) + (1912409/50000000000000 : ℝ)*(lower5) + (70599352538431/6250000000000 : ℝ)*(major0) + (70599352538431/6250000000000 : ℝ)*(major1) + (70599352538431/6250000000000 : ℝ)*(major2) + (801416311/12500000000000 : ℝ)*(sp0) + (17279670783/20000000000000 : ℝ)*(sp1) + (16230345117/20000000000000 : ℝ)*(sp2) + (11194162019/50000000000000 : ℝ)*(sp3) + (1703189954801231/100000000000000 : ℝ)*(sp8) + (425777491944451/25000000000000 : ℝ)*(sp9) + (851557607203067/50000000000000 : ℝ)*(sp10) + (264395166406403/50000000000000 : ℝ)*(sp11) + (132203180284211/25000000000000 : ℝ)*(f.failure) + (1703196366131719/100000000000000 : ℝ)*(f.sum) + (25108851382981/6405000000000000000000000000 : ℝ)*base66 + (19733192698811449/8006250000000000000000000000000 : ℝ)*base67 + (11471584580017699/8006250000000000000000000000000 : ℝ)*base69 + (45095764130144801/8006250000000000000000000000000 : ℝ)*base72 + (6423473706191/1601250000000000000000000000 : ℝ)*base73 + (3020264442813551/8006250000000000000000000000000 : ℝ)*base76 + (12775487353244801/8006250000000000000000000000000 : ℝ)*base78 + (30649297182382301/8006250000000000000000000000000 : ℝ)*base80 + (12824710953059/6405000000000000000000000000 : ℝ)*base81 + (1011549/625000000000000000000 : ℝ)*base89 + (1011549/625000000000000000000 : ℝ)*base91 + (1011549/625000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-92881/100000 : ℝ) ≤ (-81268351866933311065045715297/87500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (44043103/50000000000000 : ℝ)*(lower0) + (20882009/50000000000000 : ℝ)*(upper3) + (22869133/100000000000000 : ℝ)*(lower4) + (296324368797673/25000000000000 : ℝ)*(major0) + (296324368797673/25000000000000 : ℝ)*(major1) + (296324368797673/25000000000000 : ℝ)*(major2) + (394157863/12500000000000 : ℝ)*(sp0) + (1779250007/50000000000000 : ℝ)*(sp5) + (989854697/6250000000000 : ℝ)*(sp6) + (10099719/20000000000000 : ℝ)*(sp8) + (923329502566217/50000000000000 : ℝ)*(sp12) + (5770808282481/312500000000 : ℝ)*(sp13) + (1846646371218781/100000000000000 : ℝ)*(sp14) + (138723028406807/25000000000000 : ℝ)*(sp15) + (138723028406807/25000000000000 : ℝ)*(f.failure) + (923331104446967/50000000000000 : ℝ)*(f.sum) + (13137535986667/6405000000000000000000000000 : ℝ)*base66 + (85592267642578117/32025000000000000000000000000000 : ℝ)*base67 + (92515157272003117/32025000000000000000000000000000 : ℝ)*base69 + (165411560080846883/32025000000000000000000000000000 : ℝ)*base72 + (21389568308209/3202500000000000000000000000 : ℝ)*base73 + (116948427911296883/32025000000000000000000000000000 : ℝ)*base76 + (76025599133278117/32025000000000000000000000000000 : ℝ)*base77 + (167326935115603117/32025000000000000000000000000000 : ℝ)*base79 + (20804403201247/6405000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (903687/625000000000000000000 : ℝ)*base90 + (903687/625000000000000000000 : ℝ)*base92 + (903687/625000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1749_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (5743/1024 : ℝ) ≤ p) (hpb : p ≤ (5759/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (53402159/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3599/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2257/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(34447/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(29031/50000 : ℝ) else (20377/25000 : ℝ) ≤ X j i ∧ X j i ≤ (92881/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1749_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1749_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5743/1024 : ℝ) ≤ p) (hpb : p ≤ (5759/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (53402159/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4499/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4513/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(34447/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(29031/50000 : ℝ) else (20377/25000 : ℝ) ≤ X j i ∧ X j i ≤ (92881/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1749_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1749_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1749_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5743/1024 : ℝ) ≤ p) (hpb : p ≤ (5759/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (53402159/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4499/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4513/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(34447/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(29031/50000 : ℝ) else (20377/25000 : ℝ) ≤ X j i ∧ X j i ≤ (92881/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1749_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
