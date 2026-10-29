-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1569_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:27:10.072512+00:00
-- url     : https://prove2.me/submissions/33528675-d110-4910-8ccf-2279bdc438cf

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
theorem support_rectangle_w1569_s0_0 (p : ℝ) (hpa : (4633/1024 : ℝ) ≤ p) (hpb : p ≤ (4635/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1627012209/10000000000 : ℝ)*x 0 + (2935134869/5000000000 : ℝ)*x 1 + (4878950429/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1627012209/10000000000 : ℝ)^4635 ≤ (1215258431849/12500000000000 : ℝ)^3611 := by
    have hnat : (1627012209 : ℕ)^4635*12500000000000^3611 ≤ 1215258431849^3611*10000000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1627012209 10000000000 1215258431849 12500000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2935134869/5000000000 : ℝ)^4635 ≤ (10094494549599/20000000000000 : ℝ)^3611 := by
    have hnat : (2935134869 : ℕ)^4635*20000000000000^3611 ≤ 10094494549599^3611*5000000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2935134869 5000000000 10094494549599 20000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4878950429/10000000000 : ℝ)^4635 ≤ (39805459783527/100000000000000 : ℝ)^3611 := by
    have hnat : (4878950429 : ℕ)^4635*100000000000000^3611 ≤ 39805459783527^3611*10000000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4878950429 10000000000 39805459783527 100000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4635/1024 : ℝ)) 4635 3611 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1627012209/10000000000 : ℝ), (2935134869/5000000000 : ℝ), (4878950429/10000000000 : ℝ)] ![(1215258431849/12500000000000 : ℝ), (10094494549599/20000000000000 : ℝ), (39805459783527/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1627012209/10000000000 : ℝ)|^4635 ≤ (1215258431849/12500000000000 : ℝ)^3611
        have hw : |(-1627012209/10000000000 : ℝ)|=(1627012209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2935134869/5000000000 : ℝ)|^4635 ≤ (10094494549599/20000000000000 : ℝ)^3611
        have hw : |(2935134869/5000000000 : ℝ)|=(2935134869/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4878950429/10000000000 : ℝ)|^4635 ≤ (39805459783527/100000000000000 : ℝ)^3611
        have hw : |(4878950429/10000000000 : ℝ)|=(4878950429/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1569_s0_1 (p : ℝ) (hpa : (4633/1024 : ℝ) ≤ p) (hpb : p ≤ (4635/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2732845899/5000000000 : ℝ)*x 0 + (-544682041/2500000000 : ℝ)*x 1 + (152467201/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2732845899/5000000000 : ℝ)^4635 ≤ (2878240638913/6250000000000 : ℝ)^3611 := by
    have hnat : (2732845899 : ℕ)^4635*6250000000000^3611 ≤ 2878240638913^3611*5000000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2732845899 5000000000 2878240638913 6250000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (544682041/2500000000 : ℝ)^4635 ≤ (14142689943287/100000000000000 : ℝ)^3611 := by
    have hnat : (544682041 : ℕ)^4635*100000000000000^3611 ≤ 14142689943287^3611*2500000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      544682041 2500000000 14142689943287 100000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (152467201/312500000 : ℝ)^4635 ≤ (1243920619217/3125000000000 : ℝ)^3611 := by
    have hnat : (152467201 : ℕ)^4635*3125000000000^3611 ≤ 1243920619217^3611*312500000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      152467201 312500000 1243920619217 3125000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4635/1024 : ℝ)) 4635 3611 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2732845899/5000000000 : ℝ), (-544682041/2500000000 : ℝ), (152467201/312500000 : ℝ)] ![(2878240638913/6250000000000 : ℝ), (14142689943287/100000000000000 : ℝ), (1243920619217/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2732845899/5000000000 : ℝ)|^4635 ≤ (2878240638913/6250000000000 : ℝ)^3611
        have hw : |(2732845899/5000000000 : ℝ)|=(2732845899/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-544682041/2500000000 : ℝ)|^4635 ≤ (14142689943287/100000000000000 : ℝ)^3611
        have hw : |(-544682041/2500000000 : ℝ)|=(544682041/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(152467201/312500000 : ℝ)|^4635 ≤ (1243920619217/3125000000000 : ℝ)^3611
        have hw : |(152467201/312500000 : ℝ)|=(152467201/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1569_s0_2 (p : ℝ) (hpa : (4633/1024 : ℝ) ≤ p) (hpb : p ≤ (4635/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2732845927/5000000000 : ℝ)*x 0 + (4878950367/10000000000 : ℝ)*x 1 + (-1089364087/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2732845927/5000000000 : ℝ)^4635 ≤ (9210370165649/20000000000000 : ℝ)^3611 := by
    have hnat : (2732845927 : ℕ)^4635*20000000000000^3611 ≤ 9210370165649^3611*5000000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2732845927 5000000000 9210370165649 20000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4878950367/10000000000 : ℝ)^4635 ≤ (159221836537/400000000000 : ℝ)^3611 := by
    have hnat : (4878950367 : ℕ)^4635*400000000000^3611 ≤ 159221836537^3611*10000000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4878950367 10000000000 159221836537 400000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1089364087/5000000000 : ℝ)^4635 ≤ (14142690026607/100000000000000 : ℝ)^3611 := by
    have hnat : (1089364087 : ℕ)^4635*100000000000000^3611 ≤ 14142690026607^3611*5000000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1089364087 5000000000 14142690026607 100000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4635/1024 : ℝ)) 4635 3611 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2732845927/5000000000 : ℝ), (4878950367/10000000000 : ℝ), (-1089364087/5000000000 : ℝ)] ![(9210370165649/20000000000000 : ℝ), (159221836537/400000000000 : ℝ), (14142690026607/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2732845927/5000000000 : ℝ)|^4635 ≤ (9210370165649/20000000000000 : ℝ)^3611
        have hw : |(2732845927/5000000000 : ℝ)|=(2732845927/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4878950367/10000000000 : ℝ)|^4635 ≤ (159221836537/400000000000 : ℝ)^3611
        have hw : |(4878950367/10000000000 : ℝ)|=(4878950367/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1089364087/5000000000 : ℝ)|^4635 ≤ (14142690026607/100000000000000 : ℝ)^3611
        have hw : |(-1089364087/5000000000 : ℝ)|=(1089364087/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1569_s0_3 (p : ℝ) (hpa : (4633/1024 : ℝ) ≤ p) (hpb : p ≤ (4635/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4130108843/10000000000 : ℝ)*x 0 + (309310481/1000000000 : ℝ)*x 1 + (4243423/7812500 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4130108843/10000000000 : ℝ)^4635 ≤ (32140797102341/100000000000000 : ℝ)^3611 := by
    have hnat : (4130108843 : ℕ)^4635*100000000000000^3611 ≤ 32140797102341^3611*10000000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4130108843 10000000000 32140797102341 100000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (309310481/1000000000 : ℝ)^4635 ≤ (22175927282121/100000000000000 : ℝ)^3611 := by
    have hnat : (309310481 : ℕ)^4635*100000000000000^3611 ≤ 22175927282121^3611*1000000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      309310481 1000000000 22175927282121 100000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4243423/7812500 : ℝ)^4635 ≤ (45683275600037/100000000000000 : ℝ)^3611 := by
    have hnat : (4243423 : ℕ)^4635*100000000000000^3611 ≤ 45683275600037^3611*7812500^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4243423 7812500 45683275600037 100000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4635/1024 : ℝ)) 4635 3611 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4130108843/10000000000 : ℝ), (309310481/1000000000 : ℝ), (4243423/7812500 : ℝ)] ![(32140797102341/100000000000000 : ℝ), (22175927282121/100000000000000 : ℝ), (45683275600037/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4130108843/10000000000 : ℝ)|^4635 ≤ (32140797102341/100000000000000 : ℝ)^3611
        have hw : |(4130108843/10000000000 : ℝ)|=(4130108843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(309310481/1000000000 : ℝ)|^4635 ≤ (22175927282121/100000000000000 : ℝ)^3611
        have hw : |(309310481/1000000000 : ℝ)|=(309310481/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4243423/7812500 : ℝ)|^4635 ≤ (45683275600037/100000000000000 : ℝ)^3611
        have hw : |(4243423/7812500 : ℝ)|=(4243423/7812500 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1569_s0_4 (p : ℝ) (hpa : (4633/1024 : ℝ) ≤ p) (hpb : p ≤ (4635/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1630072957/10000000000 : ℝ)*x 0 + (1225984861/2500000000 : ℝ)*x 1 + (1461099149/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1630072957/10000000000 : ℝ)^4635 ≤ (9745549364647/100000000000000 : ℝ)^3611 := by
    have hnat : (1630072957 : ℕ)^4635*100000000000000^3611 ≤ 9745549364647^3611*10000000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1630072957 10000000000 9745549364647 100000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1225984861/2500000000 : ℝ)^4635 ≤ (20033669948051/50000000000000 : ℝ)^3611 := by
    have hnat : (1225984861 : ℕ)^4635*50000000000000^3611 ≤ 20033669948051^3611*2500000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1225984861 2500000000 20033669948051 50000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1461099149/2500000000 : ℝ)^4635 ≤ (5018711072799/10000000000000 : ℝ)^3611 := by
    have hnat : (1461099149 : ℕ)^4635*10000000000000^3611 ≤ 5018711072799^3611*2500000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1461099149 2500000000 5018711072799 10000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4635/1024 : ℝ)) 4635 3611 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1630072957/10000000000 : ℝ), (1225984861/2500000000 : ℝ), (1461099149/2500000000 : ℝ)] ![(9745549364647/100000000000000 : ℝ), (20033669948051/50000000000000 : ℝ), (5018711072799/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1630072957/10000000000 : ℝ)|^4635 ≤ (9745549364647/100000000000000 : ℝ)^3611
        have hw : |(-1630072957/10000000000 : ℝ)|=(1630072957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1225984861/2500000000 : ℝ)|^4635 ≤ (20033669948051/50000000000000 : ℝ)^3611
        have hw : |(1225984861/2500000000 : ℝ)|=(1225984861/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1461099149/2500000000 : ℝ)|^4635 ≤ (5018711072799/10000000000000 : ℝ)^3611
        have hw : |(1461099149/2500000000 : ℝ)|=(1461099149/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1569_s0_5 (p : ℝ) (hpa : (4633/1024 : ℝ) ≤ p) (hpb : p ≤ (4635/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1038937531/2000000000 : ℝ)*x 0 + (-1213285559/10000000000 : ℝ)*x 1 + (1168879579/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1038937531/2000000000 : ℝ)^4635 ≤ (21570905242249/50000000000000 : ℝ)^3611 := by
    have hnat : (1038937531 : ℕ)^4635*50000000000000^3611 ≤ 21570905242249^3611*2000000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1038937531 2000000000 21570905242249 50000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1213285559/10000000000 : ℝ)^4635 ≤ (3335532223561/50000000000000 : ℝ)^3611 := by
    have hnat : (1213285559 : ℕ)^4635*50000000000000^3611 ≤ 3335532223561^3611*10000000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1213285559 10000000000 3335532223561 50000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1168879579/2000000000 : ℝ)^4635 ≤ (50187125046041/100000000000000 : ℝ)^3611 := by
    have hnat : (1168879579 : ℕ)^4635*100000000000000^3611 ≤ 50187125046041^3611*2000000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1168879579 2000000000 50187125046041 100000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4635/1024 : ℝ)) 4635 3611 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1038937531/2000000000 : ℝ), (-1213285559/10000000000 : ℝ), (1168879579/2000000000 : ℝ)] ![(21570905242249/50000000000000 : ℝ), (3335532223561/50000000000000 : ℝ), (50187125046041/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1038937531/2000000000 : ℝ)|^4635 ≤ (21570905242249/50000000000000 : ℝ)^3611
        have hw : |(1038937531/2000000000 : ℝ)|=(1038937531/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1213285559/10000000000 : ℝ)|^4635 ≤ (3335532223561/50000000000000 : ℝ)^3611
        have hw : |(-1213285559/10000000000 : ℝ)|=(1213285559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1168879579/2000000000 : ℝ)|^4635 ≤ (50187125046041/100000000000000 : ℝ)^3611
        have hw : |(1168879579/2000000000 : ℝ)|=(1168879579/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1569_s0_6 (p : ℝ) (hpa : (4633/1024 : ℝ) ≤ p) (hpb : p ≤ (4635/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5194692787/10000000000 : ℝ)*x 0 + (1461098613/2500000000 : ℝ)*x 1 + (-606641593/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5194692787/10000000000 : ℝ)^4635 ≤ (21570932596063/50000000000000 : ℝ)^3611 := by
    have hnat : (5194692787 : ℕ)^4635*50000000000000^3611 ≤ 21570932596063^3611*10000000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5194692787 10000000000 21570932596063 50000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1461098613/2500000000 : ℝ)^4635 ≤ (25093543548021/50000000000000 : ℝ)^3611 := by
    have hnat : (1461098613 : ℕ)^4635*50000000000000^3611 ≤ 25093543548021^3611*2500000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1461098613 2500000000 25093543548021 50000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (606641593/5000000000 : ℝ)^4635 ≤ (1334209539909/20000000000000 : ℝ)^3611 := by
    have hnat : (606641593 : ℕ)^4635*20000000000000^3611 ≤ 1334209539909^3611*5000000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      606641593 5000000000 1334209539909 20000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4635/1024 : ℝ)) 4635 3611 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5194692787/10000000000 : ℝ), (1461098613/2500000000 : ℝ), (-606641593/5000000000 : ℝ)] ![(21570932596063/50000000000000 : ℝ), (25093543548021/50000000000000 : ℝ), (1334209539909/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5194692787/10000000000 : ℝ)|^4635 ≤ (21570932596063/50000000000000 : ℝ)^3611
        have hw : |(5194692787/10000000000 : ℝ)|=(5194692787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1461098613/2500000000 : ℝ)|^4635 ≤ (25093543548021/50000000000000 : ℝ)^3611
        have hw : |(1461098613/2500000000 : ℝ)|=(1461098613/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-606641593/5000000000 : ℝ)|^4635 ≤ (1334209539909/20000000000000 : ℝ)^3611
        have hw : |(-606641593/5000000000 : ℝ)|=(606641593/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1569_s0_7 (p : ℝ) (hpa : (4633/1024 : ℝ) ≤ p) (hpb : p ≤ (4635/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1034332963/2500000000 : ℝ)*x 0 + (5372636621/10000000000 : ℝ)*x 1 + (3154135621/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1034332963/2500000000 : ℝ)^4635 ≤ (32212964855767/100000000000000 : ℝ)^3611 := by
    have hnat : (1034332963 : ℕ)^4635*100000000000000^3611 ≤ 32212964855767^3611*2500000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1034332963 2500000000 32212964855767 100000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5372636621/10000000000 : ℝ)^4635 ≤ (22523951625403/50000000000000 : ℝ)^3611 := by
    have hnat : (5372636621 : ℕ)^4635*50000000000000^3611 ≤ 22523951625403^3611*10000000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5372636621 10000000000 22523951625403 50000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3154135621/10000000000 : ℝ)^4635 ≤ (22739131890627/100000000000000 : ℝ)^3611 := by
    have hnat : (3154135621 : ℕ)^4635*100000000000000^3611 ≤ 22739131890627^3611*10000000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3154135621 10000000000 22739131890627 100000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4635/1024 : ℝ)) 4635 3611 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1034332963/2500000000 : ℝ), (5372636621/10000000000 : ℝ), (3154135621/10000000000 : ℝ)] ![(32212964855767/100000000000000 : ℝ), (22523951625403/50000000000000 : ℝ), (22739131890627/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1034332963/2500000000 : ℝ)|^4635 ≤ (32212964855767/100000000000000 : ℝ)^3611
        have hw : |(1034332963/2500000000 : ℝ)|=(1034332963/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5372636621/10000000000 : ℝ)|^4635 ≤ (22523951625403/50000000000000 : ℝ)^3611
        have hw : |(5372636621/10000000000 : ℝ)|=(5372636621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3154135621/10000000000 : ℝ)|^4635 ≤ (22739131890627/100000000000000 : ℝ)^3611
        have hw : |(3154135621/10000000000 : ℝ)|=(3154135621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1569_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4633/1024 : ℝ) ≤ p) (hpb : p ≤ (4635/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (167947699/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (3533/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (24767/100000 : ℝ)*pair X 0 0 := by
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
  have base32 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1+(1 : ℝ)*X 2 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 1).2]
  have base37 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 1 2+(1 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 2).2]
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
  have hpowlo : (0 : ℝ) ^ (4633/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4633 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4633*1^1024 ≤ 0^1024*1^4633 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4633 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4633 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4633/1024 : ℝ) ≤ (1583268709286885011/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4633 ≤ (1583268709286885011/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4633*100000000000000000000^1024 ≤ 1583268709286885011^1024*5^4633 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 1583268709286885011 100000000000000000000 4633 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (1583268709286885011/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4633 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4633/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4633 := by
      have hnat : (1 : ℕ)^1024*1^4633 ≤ 1^4633*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4633 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4633 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (101583268709286885011/100000000000000000000 : ℝ) ≤ (2006956020801529/2000000000000000 : ℝ) ^ (4633/1024 : ℝ) := by
    have hpowers : (101583268709286885011/100000000000000000000 : ℝ)^1024 ≤ (2006956020801529/2000000000000000 : ℝ)^4633 := by
      have hnat : (101583268709286885011 : ℕ)^1024*2000000000000000^4633 ≤ 2006956020801529^4633*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        101583268709286885011 100000000000000000000 2006956020801529 2000000000000000 1024 4633 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2006956020801529/2000000000000000 : ℝ)) (X := (101583268709286885011/100000000000000000000 : ℝ)) (by norm_num) 4633 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (51583268709286885011/50000000000000000000 : ℝ) ≤ (1006956020801529/1000000000000000 : ℝ) ^ (4633/1024 : ℝ) := by
    have hpowers : (51583268709286885011/50000000000000000000 : ℝ)^1024 ≤ (1006956020801529/1000000000000000 : ℝ)^4633 := by
      have hnat : (51583268709286885011 : ℕ)^1024*1000000000000000^4633 ≤ 1006956020801529^4633*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51583268709286885011 50000000000000000000 1006956020801529 1000000000000000 1024 4633 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1006956020801529/1000000000000000 : ℝ)) (X := (51583268709286885011/50000000000000000000 : ℝ)) (by norm_num) 4633 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(6956020801529/800000000000000 : ℝ)*(0 : ℝ))^(4633/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(6956020801529/800000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1583268709286885011/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(6956020801529/800000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4633/1024 : ℝ) := by
    rw [show (1 : ℝ)+(6956020801529/800000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(2006956020801529/2000000000000000 : ℝ) by norm_num, show 1+(1583268709286885011/100000000000000000000 : ℝ)+(0 : ℝ)=(101583268709286885011/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1583268709286885011/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(6956020801529/800000000000000 : ℝ)*(2/5 : ℝ))^(4633/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(6956020801529/800000000000000 : ℝ)*(2/5 : ℝ)=(1006956020801529/1000000000000000 : ℝ) by norm_num, show 1+2*(1583268709286885011/100000000000000000000 : ℝ)=(51583268709286885011/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(6956020801529/800000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4633/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (6956020801529/800000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(6956020801529/800000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4633/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (6956020801529/800000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(6956020801529/800000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4633/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (6956020801529/800000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1627012209/10000000000 : ℝ)*X 0 0+(2935134869/5000000000 : ℝ)*X 0 1+(4878950429/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1569_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2732845899/5000000000 : ℝ)*X 1 0+(-544682041/2500000000 : ℝ)*X 1 1+(152467201/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1569_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2732845927/5000000000 : ℝ)*X 2 0+(4878950367/10000000000 : ℝ)*X 2 1+(-1089364087/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1569_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4130108843/10000000000 : ℝ)*X 0 0+(309310481/1000000000 : ℝ)*X 0 1+(4243423/7812500 : ℝ)*X 0 2+(4130108843/10000000000 : ℝ)*X 1 0+(309310481/1000000000 : ℝ)*X 1 1+(4243423/7812500 : ℝ)*X 1 2+(4130108843/10000000000 : ℝ)*X 2 0+(309310481/1000000000 : ℝ)*X 2 1+(4243423/7812500 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1569_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1630072957/10000000000 : ℝ)*X 0 0+(1225984861/2500000000 : ℝ)*X 0 1+(1461099149/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1569_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1038937531/2000000000 : ℝ)*X 1 0+(-1213285559/10000000000 : ℝ)*X 1 1+(1168879579/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1569_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5194692787/10000000000 : ℝ)*X 2 0+(1461098613/2500000000 : ℝ)*X 2 1+(-606641593/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1569_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1034332963/2500000000 : ℝ)*X 0 0+(5372636621/10000000000 : ℝ)*X 0 1+(3154135621/10000000000 : ℝ)*X 0 2+(1034332963/2500000000 : ℝ)*X 1 0+(5372636621/10000000000 : ℝ)*X 1 1+(3154135621/10000000000 : ℝ)*X 1 2+(1034332963/2500000000 : ℝ)*X 2 0+(5372636621/10000000000 : ℝ)*X 2 1+(3154135621/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1569_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (71468080798114362026271/40000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (823511/5000000000000 : ℝ)*(base1) + (67560173/20000000000000 : ℝ)*(base19) + (69627267/20000000000000 : ℝ)*(base23) + (1059259/2500000000000 : ℝ)*(upper3) + (21167657/50000000000000 : ℝ)*(upper5) + (718194550050911/100000000000000 : ℝ)*(major0) + (718194550050911/100000000000000 : ℝ)*(major1) + (718194550050911/100000000000000 : ℝ)*(major2) + (504378950194943/50000000000000 : ℝ)*(sp0) + (100875881896063/10000000000000 : ℝ)*(sp1) + (25218970215629/2500000000000 : ℝ)*(sp2) + (1670427057233/390625000000 : ℝ)*(sp3) + (318210457/25000000000000 : ℝ)*(sp4) + (540661721/100000000000000 : ℝ)*(sp7) + (427629883783589/100000000000000 : ℝ)*(f.failure) + (201751831352299/20000000000000 : ℝ)*(f.sum) + (50253902797081/40000000000000000000000000000 : ℝ)*base66 + (136961633037081/80000000000000000000000000000 : ℝ)*base68 + (8157541202919/80000000000000000000000000000 : ℝ)*base69 + (199491887037081/80000000000000000000000000000 : ℝ)*base72 + (48659155397081/40000000000000000000000000000 : ℝ)*base74 + (404075545037081/80000000000000000000000000000 : ℝ)*base76 + (173534599037081/80000000000000000000000000000 : ℝ)*base78 + (509609650637081/80000000000000000000000000000 : ℝ)*base80 + (39753215802919/40000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (86511711/10000000000000000000000 : ℝ)*base89 + (86511711/10000000000000000000000 : ℝ)*base91 + (86511711/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (418013128376312654988009/40000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (304863997/50000000000000 : ℝ)*(base19) + (465493049/25000000000000 : ℝ)*(base23) + (344111577/100000000000000 : ℝ)*(base32) + (102594611/100000000000000 : ℝ)*(base37) + (195751439/50000000000000 : ℝ)*(upper3) + (4859987/6250000000000 : ℝ)*(upper5) + (757033864641431/100000000000000 : ℝ)*(major0) + (757033864641431/100000000000000 : ℝ)*(major1) + (757033864641431/100000000000000 : ℝ)*(major2) + (483447987/12500000000000 : ℝ)*(sp2) + (33228489315193/3125000000000 : ℝ)*(sp4) + (531655524179091/50000000000000 : ℝ)*(sp5) + (1063305928530083/100000000000000 : ℝ)*(sp6) + (56344409518277/12500000000000 : ℝ)*(sp7) + (90151144570481/20000000000000 : ℝ)*(f.failure) + (33228489315193/3125000000000 : ℝ)*(f.sum) + (107639617547999/40000000000000000000000000000 : ℝ)*base65 + (813780619147999/80000000000000000000000000000 : ℝ)*base67 + (26964561012001/80000000000000000000000000000 : ℝ)*base70 + (377779582187999/80000000000000000000000000000 : ℝ)*base71 + (285273505627999/40000000000000000000000000000 : ℝ)*base73 + (37213839467999/80000000000000000000000000000 : ℝ)*base75 + (485959478587999/80000000000000000000000000000 : ℝ)*base77 + (1265359562827999/80000000000000000000000000000 : ℝ)*base79 + (99322790212001/40000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (7273219/2000000000000000000000 : ℝ)*base89 + (7273219/2000000000000000000000 : ℝ)*base91 + (7273219/2000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1569_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4633/1024 : ℝ) ≤ p) (hpb : p ≤ (4635/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (167947699/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (3533/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (24767/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1569_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1569_s1_0 (p : ℝ) (hpa : (4633/1024 : ℝ) ≤ p) (hpb : p ≤ (4635/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1765867769/10000000000 : ℝ)*x 0 + (2767702337/5000000000 : ℝ)*x 1 + (2562160433/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1765867769/10000000000 : ℝ)^4635 ≤ (5399855319971/50000000000000 : ℝ)^3611 := by
    have hnat : (1765867769 : ℕ)^4635*50000000000000^3611 ≤ 5399855319971^3611*10000000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1765867769 10000000000 5399855319971 50000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2767702337/5000000000 : ℝ)^4635 ≤ (1170178756973/2500000000000 : ℝ)^3611 := by
    have hnat : (2767702337 : ℕ)^4635*2500000000000^3611 ≤ 1170178756973^3611*5000000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2767702337 5000000000 1170178756973 2500000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2562160433/5000000000 : ℝ)^4635 ≤ (5299142382563/12500000000000 : ℝ)^3611 := by
    have hnat : (2562160433 : ℕ)^4635*12500000000000^3611 ≤ 5299142382563^3611*5000000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2562160433 5000000000 5299142382563 12500000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4635/1024 : ℝ)) 4635 3611 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1765867769/10000000000 : ℝ), (2767702337/5000000000 : ℝ), (2562160433/5000000000 : ℝ)] ![(5399855319971/50000000000000 : ℝ), (1170178756973/2500000000000 : ℝ), (5299142382563/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1765867769/10000000000 : ℝ)|^4635 ≤ (5399855319971/50000000000000 : ℝ)^3611
        have hw : |(-1765867769/10000000000 : ℝ)|=(1765867769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2767702337/5000000000 : ℝ)|^4635 ≤ (1170178756973/2500000000000 : ℝ)^3611
        have hw : |(2767702337/5000000000 : ℝ)|=(2767702337/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2562160433/5000000000 : ℝ)|^4635 ≤ (5299142382563/12500000000000 : ℝ)^3611
        have hw : |(2562160433/5000000000 : ℝ)|=(2562160433/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1569_s1_1 (p : ℝ) (hpa : (4633/1024 : ℝ) ≤ p) (hpb : p ≤ (4635/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (672076081/1250000000 : ℝ)*x 0 + (-1980915873/10000000000 : ℝ)*x 1 + (5124320639/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (672076081/1250000000 : ℝ)^4635 ≤ (22545328148811/50000000000000 : ℝ)^3611 := by
    have hnat : (672076081 : ℕ)^4635*50000000000000^3611 ≤ 22545328148811^3611*1250000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      672076081 1250000000 22545328148811 50000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1980915873/10000000000 : ℝ)^4635 ≤ (6258103517857/50000000000000 : ℝ)^3611 := by
    have hnat : (1980915873 : ℕ)^4635*50000000000000^3611 ≤ 6258103517857^3611*10000000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1980915873 10000000000 6258103517857 50000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5124320639/10000000000 : ℝ)^4635 ≤ (21196568325001/50000000000000 : ℝ)^3611 := by
    have hnat : (5124320639 : ℕ)^4635*50000000000000^3611 ≤ 21196568325001^3611*10000000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5124320639 10000000000 21196568325001 50000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4635/1024 : ℝ)) 4635 3611 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(672076081/1250000000 : ℝ), (-1980915873/10000000000 : ℝ), (5124320639/10000000000 : ℝ)] ![(22545328148811/50000000000000 : ℝ), (6258103517857/50000000000000 : ℝ), (21196568325001/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(672076081/1250000000 : ℝ)|^4635 ≤ (22545328148811/50000000000000 : ℝ)^3611
        have hw : |(672076081/1250000000 : ℝ)|=(672076081/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1980915873/10000000000 : ℝ)|^4635 ≤ (6258103517857/50000000000000 : ℝ)^3611
        have hw : |(-1980915873/10000000000 : ℝ)|=(1980915873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5124320639/10000000000 : ℝ)|^4635 ≤ (21196568325001/50000000000000 : ℝ)^3611
        have hw : |(5124320639/10000000000 : ℝ)|=(5124320639/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1569_s1_2 (p : ℝ) (hpa : (4633/1024 : ℝ) ≤ p) (hpb : p ≤ (4635/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5376608551/10000000000 : ℝ)*x 0 + (5124321037/10000000000 : ℝ)*x 1 + (-49522887/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5376608551/10000000000 : ℝ)^4635 ≤ (901813105069/2000000000000 : ℝ)^3611 := by
    have hnat : (5376608551 : ℕ)^4635*2000000000000^3611 ≤ 901813105069^3611*10000000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5376608551 10000000000 901813105069 2000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5124321037/10000000000 : ℝ)^4635 ≤ (5299142609543/12500000000000 : ℝ)^3611 := by
    have hnat : (5124321037 : ℕ)^4635*12500000000000^3611 ≤ 5299142609543^3611*10000000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5124321037 10000000000 5299142609543 12500000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (49522887/250000000 : ℝ)^4635 ≤ (500648153937/4000000000000 : ℝ)^3611 := by
    have hnat : (49522887 : ℕ)^4635*4000000000000^3611 ≤ 500648153937^3611*250000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      49522887 250000000 500648153937 4000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4635/1024 : ℝ)) 4635 3611 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5376608551/10000000000 : ℝ), (5124321037/10000000000 : ℝ), (-49522887/250000000 : ℝ)] ![(901813105069/2000000000000 : ℝ), (5299142609543/12500000000000 : ℝ), (500648153937/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5376608551/10000000000 : ℝ)|^4635 ≤ (901813105069/2000000000000 : ℝ)^3611
        have hw : |(5376608551/10000000000 : ℝ)|=(5376608551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5124321037/10000000000 : ℝ)|^4635 ≤ (5299142609543/12500000000000 : ℝ)^3611
        have hw : |(5124321037/10000000000 : ℝ)|=(5124321037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-49522887/250000000 : ℝ)|^4635 ≤ (500648153937/4000000000000 : ℝ)^3611
        have hw : |(-49522887/250000000 : ℝ)|=(49522887/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1569_s1_3 (p : ℝ) (hpa : (4633/1024 : ℝ) ≤ p) (hpb : p ≤ (4635/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2114411711/5000000000 : ℝ)*x 0 + (3766383529/10000000000 : ℝ)*x 1 + (947222573/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2114411711/5000000000 : ℝ)^4635 ≤ (33130169319229/100000000000000 : ℝ)^3611 := by
    have hnat : (2114411711 : ℕ)^4635*100000000000000^3611 ≤ 33130169319229^3611*5000000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2114411711 5000000000 33130169319229 100000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3766383529/10000000000 : ℝ)^4635 ≤ (28553943131439/100000000000000 : ℝ)^3611 := by
    have hnat : (3766383529 : ℕ)^4635*100000000000000^3611 ≤ 28553943131439^3611*10000000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3766383529 10000000000 28553943131439 100000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (947222573/2000000000 : ℝ)^4635 ≤ (38315887532117/100000000000000 : ℝ)^3611 := by
    have hnat : (947222573 : ℕ)^4635*100000000000000^3611 ≤ 38315887532117^3611*2000000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      947222573 2000000000 38315887532117 100000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4635/1024 : ℝ)) 4635 3611 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2114411711/5000000000 : ℝ), (3766383529/10000000000 : ℝ), (947222573/2000000000 : ℝ)] ![(33130169319229/100000000000000 : ℝ), (28553943131439/100000000000000 : ℝ), (38315887532117/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2114411711/5000000000 : ℝ)|^4635 ≤ (33130169319229/100000000000000 : ℝ)^3611
        have hw : |(2114411711/5000000000 : ℝ)|=(2114411711/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3766383529/10000000000 : ℝ)|^4635 ≤ (28553943131439/100000000000000 : ℝ)^3611
        have hw : |(3766383529/10000000000 : ℝ)|=(3766383529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(947222573/2000000000 : ℝ)|^4635 ≤ (38315887532117/100000000000000 : ℝ)^3611
        have hw : |(947222573/2000000000 : ℝ)|=(947222573/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1569_s1_4 (p : ℝ) (hpa : (4633/1024 : ℝ) ≤ p) (hpb : p ≤ (4635/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1766080283/10000000000 : ℝ)*x 0 + (2564283863/5000000000 : ℝ)*x 1 + (553109507/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1766080283/10000000000 : ℝ)^4635 ≤ (10801378928403/100000000000000 : ℝ)^3611 := by
    have hnat : (1766080283 : ℕ)^4635*100000000000000^3611 ≤ 10801378928403^3611*10000000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1766080283 10000000000 10801378928403 100000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2564283863/5000000000 : ℝ)^4635 ≤ (42438241545963/100000000000000 : ℝ)^3611 := by
    have hnat : (2564283863 : ℕ)^4635*100000000000000^3611 ≤ 42438241545963^3611*5000000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2564283863 5000000000 42438241545963 100000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (553109507/1000000000 : ℝ)^4635 ≤ (46760379512429/100000000000000 : ℝ)^3611 := by
    have hnat : (553109507 : ℕ)^4635*100000000000000^3611 ≤ 46760379512429^3611*1000000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      553109507 1000000000 46760379512429 100000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4635/1024 : ℝ)) 4635 3611 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1766080283/10000000000 : ℝ), (2564283863/5000000000 : ℝ), (553109507/1000000000 : ℝ)] ![(10801378928403/100000000000000 : ℝ), (42438241545963/100000000000000 : ℝ), (46760379512429/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1766080283/10000000000 : ℝ)|^4635 ≤ (10801378928403/100000000000000 : ℝ)^3611
        have hw : |(-1766080283/10000000000 : ℝ)|=(1766080283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2564283863/5000000000 : ℝ)|^4635 ≤ (42438241545963/100000000000000 : ℝ)^3611
        have hw : |(2564283863/5000000000 : ℝ)|=(2564283863/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(553109507/1000000000 : ℝ)|^4635 ≤ (46760379512429/100000000000000 : ℝ)^3611
        have hw : |(553109507/1000000000 : ℝ)|=(553109507/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1569_s1_5 (p : ℝ) (hpa : (4633/1024 : ℝ) ≤ p) (hpb : p ≤ (4635/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (658456709/1250000000 : ℝ)*x 0 + (-393535349/2500000000 : ℝ)*x 1 + (691386939/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (658456709/1250000000 : ℝ)^4635 ≤ (1372536853027/3125000000000 : ℝ)^3611 := by
    have hnat : (658456709 : ℕ)^4635*3125000000000^3611 ≤ 1372536853027^3611*1250000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658456709 1250000000 1372536853027 3125000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (393535349/2500000000 : ℝ)^4635 ≤ (9318436385569/100000000000000 : ℝ)^3611 := by
    have hnat : (393535349 : ℕ)^4635*100000000000000^3611 ≤ 9318436385569^3611*2500000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      393535349 2500000000 9318436385569 100000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (691386939/1250000000 : ℝ)^4635 ≤ (9352076861757/20000000000000 : ℝ)^3611 := by
    have hnat : (691386939 : ℕ)^4635*20000000000000^3611 ≤ 9352076861757^3611*1250000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      691386939 1250000000 9352076861757 20000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4635/1024 : ℝ)) 4635 3611 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(658456709/1250000000 : ℝ), (-393535349/2500000000 : ℝ), (691386939/1250000000 : ℝ)] ![(1372536853027/3125000000000 : ℝ), (9318436385569/100000000000000 : ℝ), (9352076861757/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(658456709/1250000000 : ℝ)|^4635 ≤ (1372536853027/3125000000000 : ℝ)^3611
        have hw : |(658456709/1250000000 : ℝ)|=(658456709/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-393535349/2500000000 : ℝ)|^4635 ≤ (9318436385569/100000000000000 : ℝ)^3611
        have hw : |(-393535349/2500000000 : ℝ)|=(393535349/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(691386939/1250000000 : ℝ)|^4635 ≤ (9352076861757/20000000000000 : ℝ)^3611
        have hw : |(691386939/1250000000 : ℝ)|=(691386939/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1569_s1_6 (p : ℝ) (hpa : (4633/1024 : ℝ) ≤ p) (hpb : p ≤ (4635/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (658456647/1250000000 : ℝ)*x 0 + (2765547847/5000000000 : ℝ)*x 1 + (-787070917/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (658456647/1250000000 : ℝ)^4635 ≤ (87842347977/200000000000 : ℝ)^3611 := by
    have hnat : (658456647 : ℕ)^4635*200000000000^3611 ≤ 87842347977^3611*1250000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658456647 1250000000 87842347977 200000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2765547847/5000000000 : ℝ)^4635 ≤ (11690096570939/25000000000000 : ℝ)^3611 := by
    have hnat : (2765547847 : ℕ)^4635*25000000000000^3611 ≤ 11690096570939^3611*5000000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2765547847 5000000000 11690096570939 25000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (787070917/5000000000 : ℝ)^4635 ≤ (72800310263/781250000000 : ℝ)^3611 := by
    have hnat : (787070917 : ℕ)^4635*781250000000^3611 ≤ 72800310263^3611*5000000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      787070917 5000000000 72800310263 781250000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4635/1024 : ℝ)) 4635 3611 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(658456647/1250000000 : ℝ), (2765547847/5000000000 : ℝ), (-787070917/5000000000 : ℝ)] ![(87842347977/200000000000 : ℝ), (11690096570939/25000000000000 : ℝ), (72800310263/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(658456647/1250000000 : ℝ)|^4635 ≤ (87842347977/200000000000 : ℝ)^3611
        have hw : |(658456647/1250000000 : ℝ)|=(658456647/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2765547847/5000000000 : ℝ)|^4635 ≤ (11690096570939/25000000000000 : ℝ)^3611
        have hw : |(2765547847/5000000000 : ℝ)|=(2765547847/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-787070917/5000000000 : ℝ)|^4635 ≤ (72800310263/781250000000 : ℝ)^3611
        have hw : |(-787070917/5000000000 : ℝ)|=(787070917/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1569_s1_7 (p : ℝ) (hpa : (4633/1024 : ℝ) ≤ p) (hpb : p ≤ (4635/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4229323559/10000000000 : ℝ)*x 0 + (4726094967/10000000000 : ℝ)*x 1 + (188827497/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4229323559/10000000000 : ℝ)^4635 ≤ (258868740577/781250000000 : ℝ)^3611 := by
    have hnat : (4229323559 : ℕ)^4635*781250000000^3611 ≤ 258868740577^3611*10000000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4229323559 10000000000 258868740577 781250000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4726094967/10000000000 : ℝ)^4635 ≤ (38211889441583/100000000000000 : ℝ)^3611 := by
    have hnat : (4726094967 : ℕ)^4635*100000000000000^3611 ≤ 38211889441583^3611*10000000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4726094967 10000000000 38211889441583 100000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (188827497/500000000 : ℝ)^4635 ≤ (5730582351333/20000000000000 : ℝ)^3611 := by
    have hnat : (188827497 : ℕ)^4635*20000000000000^3611 ≤ 5730582351333^3611*500000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      188827497 500000000 5730582351333 20000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4635/1024 : ℝ)) 4635 3611 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4229323559/10000000000 : ℝ), (4726094967/10000000000 : ℝ), (188827497/500000000 : ℝ)] ![(258868740577/781250000000 : ℝ), (38211889441583/100000000000000 : ℝ), (5730582351333/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4229323559/10000000000 : ℝ)|^4635 ≤ (258868740577/781250000000 : ℝ)^3611
        have hw : |(4229323559/10000000000 : ℝ)|=(4229323559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4726094967/10000000000 : ℝ)|^4635 ≤ (38211889441583/100000000000000 : ℝ)^3611
        have hw : |(4726094967/10000000000 : ℝ)|=(4726094967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(188827497/500000000 : ℝ)|^4635 ≤ (5730582351333/20000000000000 : ℝ)^3611
        have hw : |(188827497/500000000 : ℝ)|=(188827497/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1569_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4633/1024 : ℝ) ≤ p) (hpb : p ≤ (4635/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (167947699/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (24767/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3533/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (4529/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4441/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (24767/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (3533/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (24767/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (3533/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (24767/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (3533/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (24767/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (3533/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (24767/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (3533/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (24767/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (3533/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (3533/100000 : ℝ) ^ (4633/1024 : ℝ) ≤ (134949307663/500000000000000000 : ℝ) := by
    have hpowers : (3533/100000 : ℝ)^4633 ≤ (134949307663/500000000000000000 : ℝ)^1024 := by
      have hnat : (3533 : ℕ)^4633*500000000000000000^1024 ≤ 134949307663^1024*100000^4633 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3533 100000 134949307663 500000000000000000 4633 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3533/100000 : ℝ)) (X := (134949307663/500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4633 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (24767/100000 : ℝ) ^ (4633/1024 : ℝ) ≤ (45245179420058531/25000000000000000000 : ℝ) := by
    have hpowers : (24767/100000 : ℝ)^4633 ≤ (45245179420058531/25000000000000000000 : ℝ)^1024 := by
      have hnat : (24767 : ℕ)^4633*25000000000000000000^1024 ≤ 45245179420058531^1024*100000^4633 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        24767 100000 45245179420058531 25000000000000000000 4633 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (24767/100000 : ℝ)) (X := (45245179420058531/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4633 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (250000134949307663/250000000000000000 : ℝ) ≤ (10000001193076297/10000000000000000 : ℝ) ^ (4633/1024 : ℝ) := by
    have hpowers : (250000134949307663/250000000000000000 : ℝ)^1024 ≤ (10000001193076297/10000000000000000 : ℝ)^4633 := by
      have hnat : (250000134949307663 : ℕ)^1024*10000000000000000^4633 ≤ 10000001193076297^4633*250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        250000134949307663 250000000000000000 10000001193076297 10000000000000000 1024 4633 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000001193076297/10000000000000000 : ℝ)) (X := (250000134949307663/250000000000000000 : ℝ)) (by norm_num) 4633 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25045251926885441681/25000000000000000000 : ℝ) ≤ (5001998935449593/5000000000000000 : ℝ) ^ (4633/1024 : ℝ) := by
    have hpowers : (25045251926885441681/25000000000000000000 : ℝ)^1024 ≤ (5001998935449593/5000000000000000 : ℝ)^4633 := by
      have hnat : (25045251926885441681 : ℕ)^1024*5000000000000000^4633 ≤ 5001998935449593^4633*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25045251926885441681 25000000000000000000 5001998935449593 5000000000000000 1024 4633 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001998935449593/5000000000000000 : ℝ)) (X := (25045251926885441681/25000000000000000000 : ℝ)) (by norm_num) 4633 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12545245179420058531/12500000000000000000 : ℝ) ≤ (400319781948883/400000000000000 : ℝ) ^ (4633/1024 : ℝ) := by
    have hpowers : (12545245179420058531/12500000000000000000 : ℝ)^1024 ≤ (400319781948883/400000000000000 : ℝ)^4633 := by
      have hnat : (12545245179420058531 : ℕ)^1024*400000000000000^4633 ≤ 400319781948883^4633*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12545245179420058531 12500000000000000000 400319781948883 400000000000000 1024 4633 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400319781948883/400000000000000 : ℝ)) (X := (12545245179420058531/12500000000000000000 : ℝ)) (by norm_num) 4633 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(134949307663/500000000000000000 : ℝ) ≤ ((8846324367011898201/8847500000000000000 : ℝ)+2*(1332225940963/707800000000000 : ℝ)*(3533/100000 : ℝ))^(4633/1024 : ℝ) := by
    rw [show (8846324367011898201/8847500000000000000 : ℝ)+2*(1332225940963/707800000000000 : ℝ)*(3533/100000 : ℝ)=(10000001193076297/10000000000000000 : ℝ) by norm_num, show 1+2*(134949307663/500000000000000000 : ℝ)=(250000134949307663/250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(45245179420058531/25000000000000000000 : ℝ)+(134949307663/500000000000000000 : ℝ) ≤ ((8846324367011898201/8847500000000000000 : ℝ)+(1332225940963/707800000000000 : ℝ)*((24767/100000 : ℝ)+(3533/100000 : ℝ)))^(4633/1024 : ℝ) := by
    rw [show (8846324367011898201/8847500000000000000 : ℝ)+(1332225940963/707800000000000 : ℝ)*((24767/100000 : ℝ)+(3533/100000 : ℝ))=(5001998935449593/5000000000000000 : ℝ) by norm_num, show 1+(45245179420058531/25000000000000000000 : ℝ)+(134949307663/500000000000000000 : ℝ)=(25045251926885441681/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(45245179420058531/25000000000000000000 : ℝ) ≤ ((8846324367011898201/8847500000000000000 : ℝ)+2*(1332225940963/707800000000000 : ℝ)*(24767/100000 : ℝ))^(4633/1024 : ℝ) := by
    rw [show (8846324367011898201/8847500000000000000 : ℝ)+2*(1332225940963/707800000000000 : ℝ)*(24767/100000 : ℝ)=(400319781948883/400000000000000 : ℝ) by norm_num, show 1+2*(45245179420058531/25000000000000000000 : ℝ)=(12545245179420058531/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (8846324367011898201/8847500000000000000 : ℝ)*(X 1 0+X 2 0)+(1332225940963/707800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4633/1024 : ℝ)) (lo := (3533/100000 : ℝ)) (hi := (24767/100000 : ℝ)) (c := (8846324367011898201/8847500000000000000 : ℝ)) (alpha := (1332225940963/707800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (8846324367011898201/8847500000000000000 : ℝ)*(X 0 1+X 2 1)+(1332225940963/707800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4633/1024 : ℝ)) (lo := (3533/100000 : ℝ)) (hi := (24767/100000 : ℝ)) (c := (8846324367011898201/8847500000000000000 : ℝ)) (alpha := (1332225940963/707800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (8846324367011898201/8847500000000000000 : ℝ)*(X 0 2+X 1 2)+(1332225940963/707800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4633/1024 : ℝ)) (lo := (3533/100000 : ℝ)) (hi := (24767/100000 : ℝ)) (c := (8846324367011898201/8847500000000000000 : ℝ)) (alpha := (1332225940963/707800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1765867769/10000000000 : ℝ)*X 0 0+(2767702337/5000000000 : ℝ)*X 0 1+(2562160433/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1569_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((672076081/1250000000 : ℝ)*X 1 0+(-1980915873/10000000000 : ℝ)*X 1 1+(5124320639/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1569_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5376608551/10000000000 : ℝ)*X 2 0+(5124321037/10000000000 : ℝ)*X 2 1+(-49522887/250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1569_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2114411711/5000000000 : ℝ)*X 0 0+(3766383529/10000000000 : ℝ)*X 0 1+(947222573/2000000000 : ℝ)*X 0 2+(2114411711/5000000000 : ℝ)*X 1 0+(3766383529/10000000000 : ℝ)*X 1 1+(947222573/2000000000 : ℝ)*X 1 2+(2114411711/5000000000 : ℝ)*X 2 0+(3766383529/10000000000 : ℝ)*X 2 1+(947222573/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1569_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1766080283/10000000000 : ℝ)*X 0 0+(2564283863/5000000000 : ℝ)*X 0 1+(553109507/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1569_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((658456709/1250000000 : ℝ)*X 1 0+(-393535349/2500000000 : ℝ)*X 1 1+(691386939/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1569_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((658456647/1250000000 : ℝ)*X 2 0+(2765547847/5000000000 : ℝ)*X 2 1+(-787070917/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1569_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4229323559/10000000000 : ℝ)*X 0 0+(4726094967/10000000000 : ℝ)*X 0 1+(188827497/500000000 : ℝ)*X 0 2+(4229323559/10000000000 : ℝ)*X 1 0+(4726094967/10000000000 : ℝ)*X 1 1+(188827497/500000000 : ℝ)*X 1 2+(4229323559/10000000000 : ℝ)*X 2 0+(4726094967/10000000000 : ℝ)*X 2 1+(188827497/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1569_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (609131891440132505619942813/110593750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (81807299/100000000000000 : ℝ)*(base1) + (1536697533/100000000000000 : ℝ)*(base19) + (298562079/20000000000000 : ℝ)*(base23) + (3159437/6250000000000 : ℝ)*(upper3) + (133159317/50000000000000 : ℝ)*(upper5) + (432981022247357/25000000000000 : ℝ)*(major0) + (432981022247357/25000000000000 : ℝ)*(major1) + (432981022247357/25000000000000 : ℝ)*(major2) + (1216302527348557/50000000000000 : ℝ)*(sp0) + (1216309112275691/50000000000000 : ℝ)*(sp1) + (60815456710963/2500000000000 : ℝ)*(sp2) + (1031222471130499/100000000000000 : ℝ)*(sp3) + (147883591/1000000000000 : ℝ)*(sp4) + (710024713/12500000000000 : ℝ)*(sp7) + (2062456466271/200000000000 : ℝ)*(f.failure) + (1216309880624457/50000000000000 : ℝ)*(f.sum) + (1930400055361/8847500000000000000000000000 : ℝ)*base65 + (1553242858872620243/221187500000000000000000000000000 : ℝ)*base68 + (3664411398923620243/221187500000000000000000000000000 : ℝ)*base70 + (3639435466249182743/221187500000000000000000000000000 : ℝ)*base72 + (60776624192747/17695000000000000000000000000 : ℝ)*base73 + (1301853603210245243/221187500000000000000000000000000 : ℝ)*base76 + (2238927749397682743/221187500000000000000000000000000 : ℝ)*base78 + (1537500458769870243/221187500000000000000000000000000 : ℝ)*base80 + (62490241312943/17695000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (39571/20000000000000000000 : ℝ)*base90 + (39571/20000000000000000000 : ℝ)*base92 + (39571/20000000000000000000 : ℝ)*base94 + (1/50000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1932169704246800460025770327/442375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (150171859/20000000000000 : ℝ)*(base19) + (657737861/100000000000000 : ℝ)*(base23) + (80894451/100000000000000 : ℝ)*(upper2) + (90905441/50000000000000 : ℝ)*(upper3) + (6260813/10000000000000 : ℝ)*(upper5) + (1768717956853691/100000000000000 : ℝ)*(major0) + (1768717956853691/100000000000000 : ℝ)*(major1) + (1768717956853691/100000000000000 : ℝ)*(major2) + (3239470107/50000000000000 : ℝ)*(sp1) + (1465391399/25000000000000 : ℝ)*(sp2) + (2484299602878963/100000000000000 : ℝ)*(sp4) + (2484292373079453/100000000000000 : ℝ)*(sp5) + (1242146541787753/50000000000000 : ℝ)*(sp6) + (1053136165237781/100000000000000 : ℝ)*(sp7) + (1053136165237781/100000000000000 : ℝ)*(f.failure) + (2484299602878963/100000000000000 : ℝ)*(f.sum) + (216634321565067/35390000000000000000000000000 : ℝ)*base66 + (780605050664772391/884750000000000000000000000000000 : ℝ)*base67 + (262426003263977609/884750000000000000000000000000000 : ℝ)*base70 + (2724083792970272391/884750000000000000000000000000000 : ℝ)*base71 + (96909915007197/35390000000000000000000000000 : ℝ)*base74 + (9028352085834022391/884750000000000000000000000000000 : ℝ)*base75 + (1086663952578727609/884750000000000000000000000000000 : ℝ)*base78 + (450977213154272391/884750000000000000000000000000000 : ℝ)*base79 + (76728556547407/35390000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (6815919/10000000000000000000000 : ℝ)*base89 + (6815919/10000000000000000000000 : ℝ)*base91 + (6815919/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1569_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4633/1024 : ℝ) ≤ p) (hpb : p ≤ (4635/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (167947699/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (24767/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3533/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4529/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4441/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1569_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1569_s2_0 (p : ℝ) (hpa : (4633/1024 : ℝ) ≤ p) (hpb : p ≤ (4635/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-892278797/5000000000 : ℝ)*x 0 + (2720850499/5000000000 : ℝ)*x 1 + (1301461591/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (892278797/5000000000 : ℝ)^4635 ≤ (10946647595709/100000000000000 : ℝ)^3611 := by
    have hnat : (892278797 : ℕ)^4635*100000000000000^3611 ≤ 10946647595709^3611*5000000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      892278797 5000000000 10946647595709 100000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2720850499/5000000000 : ℝ)^4635 ≤ (45792552758753/100000000000000 : ℝ)^3611 := by
    have hnat : (2720850499 : ℕ)^4635*100000000000000^3611 ≤ 45792552758753^3611*5000000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2720850499 5000000000 45792552758753 100000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1301461591/2500000000 : ℝ)^4635 ≤ (21630399811129/50000000000000 : ℝ)^3611 := by
    have hnat : (1301461591 : ℕ)^4635*50000000000000^3611 ≤ 21630399811129^3611*2500000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1301461591 2500000000 21630399811129 50000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4635/1024 : ℝ)) 4635 3611 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-892278797/5000000000 : ℝ), (2720850499/5000000000 : ℝ), (1301461591/2500000000 : ℝ)] ![(10946647595709/100000000000000 : ℝ), (45792552758753/100000000000000 : ℝ), (21630399811129/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-892278797/5000000000 : ℝ)|^4635 ≤ (10946647595709/100000000000000 : ℝ)^3611
        have hw : |(-892278797/5000000000 : ℝ)|=(892278797/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2720850499/5000000000 : ℝ)|^4635 ≤ (45792552758753/100000000000000 : ℝ)^3611
        have hw : |(2720850499/5000000000 : ℝ)|=(2720850499/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1301461591/2500000000 : ℝ)|^4635 ≤ (21630399811129/50000000000000 : ℝ)^3611
        have hw : |(1301461591/2500000000 : ℝ)|=(1301461591/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1569_s2_1 (p : ℝ) (hpa : (4633/1024 : ℝ) ≤ p) (hpb : p ≤ (4635/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5352412599/10000000000 : ℝ)*x 0 + (-190561681/1000000000 : ℝ)*x 1 + (5205846169/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5352412599/10000000000 : ℝ)^4635 ≤ (22415180197487/50000000000000 : ℝ)^3611 := by
    have hnat : (5352412599 : ℕ)^4635*50000000000000^3611 ≤ 22415180197487^3611*10000000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5352412599 10000000000 22415180197487 50000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (190561681/1000000000 : ℝ)^4635 ≤ (2977210511801/25000000000000 : ℝ)^3611 := by
    have hnat : (190561681 : ℕ)^4635*25000000000000^3611 ≤ 2977210511801^3611*1000000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      190561681 1000000000 2977210511801 25000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5205846169/10000000000 : ℝ)^4635 ≤ (21630398771137/50000000000000 : ℝ)^3611 := by
    have hnat : (5205846169 : ℕ)^4635*50000000000000^3611 ≤ 21630398771137^3611*10000000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5205846169 10000000000 21630398771137 50000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4635/1024 : ℝ)) 4635 3611 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5352412599/10000000000 : ℝ), (-190561681/1000000000 : ℝ), (5205846169/10000000000 : ℝ)] ![(22415180197487/50000000000000 : ℝ), (2977210511801/25000000000000 : ℝ), (21630398771137/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5352412599/10000000000 : ℝ)|^4635 ≤ (22415180197487/50000000000000 : ℝ)^3611
        have hw : |(5352412599/10000000000 : ℝ)|=(5352412599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-190561681/1000000000 : ℝ)|^4635 ≤ (2977210511801/25000000000000 : ℝ)^3611
        have hw : |(-190561681/1000000000 : ℝ)|=(190561681/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5205846169/10000000000 : ℝ)|^4635 ≤ (21630398771137/50000000000000 : ℝ)^3611
        have hw : |(5205846169/10000000000 : ℝ)|=(5205846169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1569_s2_2 (p : ℝ) (hpa : (4633/1024 : ℝ) ≤ p) (hpb : p ≤ (4635/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5352412591/10000000000 : ℝ)*x 0 + (5205846097/10000000000 : ℝ)*x 1 + (-476404229/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5352412591/10000000000 : ℝ)^4635 ≤ (44830360308967/100000000000000 : ℝ)^3611 := by
    have hnat : (5352412591 : ℕ)^4635*100000000000000^3611 ≤ 44830360308967^3611*10000000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5352412591 10000000000 44830360308967 100000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5205846097/10000000000 : ℝ)^4635 ≤ (1081519919357/2500000000000 : ℝ)^3611 := by
    have hnat : (5205846097 : ℕ)^4635*2500000000000^3611 ≤ 1081519919357^3611*10000000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5205846097 10000000000 1081519919357 2500000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (476404229/2500000000 : ℝ)^4635 ≤ (2977210724371/25000000000000 : ℝ)^3611 := by
    have hnat : (476404229 : ℕ)^4635*25000000000000^3611 ≤ 2977210724371^3611*2500000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      476404229 2500000000 2977210724371 25000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4635/1024 : ℝ)) 4635 3611 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5352412591/10000000000 : ℝ), (5205846097/10000000000 : ℝ), (-476404229/2500000000 : ℝ)] ![(44830360308967/100000000000000 : ℝ), (1081519919357/2500000000000 : ℝ), (2977210724371/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5352412591/10000000000 : ℝ)|^4635 ≤ (44830360308967/100000000000000 : ℝ)^3611
        have hw : |(5352412591/10000000000 : ℝ)|=(5352412591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5205846097/10000000000 : ℝ)|^4635 ≤ (1081519919357/2500000000000 : ℝ)^3611
        have hw : |(5205846097/10000000000 : ℝ)|=(5205846097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-476404229/2500000000 : ℝ)|^4635 ≤ (2977210724371/25000000000000 : ℝ)^3611
        have hw : |(-476404229/2500000000 : ℝ)|=(476404229/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1569_s2_3 (p : ℝ) (hpa : (4633/1024 : ℝ) ≤ p) (hpb : p ≤ (4635/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4242365391/10000000000 : ℝ)*x 0 + (794313471/2000000000 : ℝ)*x 1 + (2263969133/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4242365391/10000000000 : ℝ)^4635 ≤ (16633204742941/50000000000000 : ℝ)^3611 := by
    have hnat : (4242365391 : ℕ)^4635*50000000000000^3611 ≤ 16633204742941^3611*10000000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4242365391 10000000000 16633204742941 50000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (794313471/2000000000 : ℝ)^4635 ≤ (30565842902089/100000000000000 : ℝ)^3611 := by
    have hnat : (794313471 : ℕ)^4635*100000000000000^3611 ≤ 30565842902089^3611*2000000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      794313471 2000000000 30565842902089 100000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2263969133/5000000000 : ℝ)^4635 ≤ (361677475979/1000000000000 : ℝ)^3611 := by
    have hnat : (2263969133 : ℕ)^4635*1000000000000^3611 ≤ 361677475979^3611*5000000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2263969133 5000000000 361677475979 1000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4635/1024 : ℝ)) 4635 3611 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4242365391/10000000000 : ℝ), (794313471/2000000000 : ℝ), (2263969133/5000000000 : ℝ)] ![(16633204742941/50000000000000 : ℝ), (30565842902089/100000000000000 : ℝ), (361677475979/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4242365391/10000000000 : ℝ)|^4635 ≤ (16633204742941/50000000000000 : ℝ)^3611
        have hw : |(4242365391/10000000000 : ℝ)|=(4242365391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(794313471/2000000000 : ℝ)|^4635 ≤ (30565842902089/100000000000000 : ℝ)^3611
        have hw : |(794313471/2000000000 : ℝ)|=(794313471/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2263969133/5000000000 : ℝ)|^4635 ≤ (361677475979/1000000000000 : ℝ)^3611
        have hw : |(2263969133/5000000000 : ℝ)|=(2263969133/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1569_s2_4 (p : ℝ) (hpa : (4633/1024 : ℝ) ≤ p) (hpb : p ≤ (4635/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-111537371/625000000 : ℝ)*x 0 + (1301812903/2500000000 : ℝ)*x 1 + (1088056757/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (111537371/625000000 : ℝ)^4635 ≤ (10946965233111/100000000000000 : ℝ)^3611 := by
    have hnat : (111537371 : ℕ)^4635*100000000000000^3611 ≤ 10946965233111^3611*625000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      111537371 625000000 10946965233111 100000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1301812903/2500000000 : ℝ)^4635 ≤ (43275789394783/100000000000000 : ℝ)^3611 := by
    have hnat : (1301812903 : ℕ)^4635*100000000000000^3611 ≤ 43275789394783^3611*2500000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1301812903 2500000000 43275789394783 100000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1088056757/2000000000 : ℝ)^4635 ≤ (22888622677837/50000000000000 : ℝ)^3611 := by
    have hnat : (1088056757 : ℕ)^4635*50000000000000^3611 ≤ 22888622677837^3611*2000000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1088056757 2000000000 22888622677837 50000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4635/1024 : ℝ)) 4635 3611 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-111537371/625000000 : ℝ), (1301812903/2500000000 : ℝ), (1088056757/2000000000 : ℝ)] ![(10946965233111/100000000000000 : ℝ), (43275789394783/100000000000000 : ℝ), (22888622677837/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-111537371/625000000 : ℝ)|^4635 ≤ (10946965233111/100000000000000 : ℝ)^3611
        have hw : |(-111537371/625000000 : ℝ)|=(111537371/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1301812903/2500000000 : ℝ)|^4635 ≤ (43275789394783/100000000000000 : ℝ)^3611
        have hw : |(1301812903/2500000000 : ℝ)|=(1301812903/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1088056757/2000000000 : ℝ)|^4635 ≤ (22888622677837/50000000000000 : ℝ)^3611
        have hw : |(1088056757/2000000000 : ℝ)|=(1088056757/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1569_s2_5 (p : ℝ) (hpa : (4633/1024 : ℝ) ≤ p) (hpb : p ≤ (4635/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1058002859/2000000000 : ℝ)*x 0 + (-1671179349/10000000000 : ℝ)*x 1 + (5440283737/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1058002859/2000000000 : ℝ)^4635 ≤ (44160634334301/100000000000000 : ℝ)^3611 := by
    have hnat : (1058002859 : ℕ)^4635*100000000000000^3611 ≤ 44160634334301^3611*2000000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1058002859 2000000000 44160634334301 100000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1671179349/10000000000 : ℝ)^4635 ≤ (10062120820093/100000000000000 : ℝ)^3611 := by
    have hnat : (1671179349 : ℕ)^4635*100000000000000^3611 ≤ 10062120820093^3611*10000000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1671179349 10000000000 10062120820093 100000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5440283737/10000000000 : ℝ)^4635 ≤ (22888622418621/50000000000000 : ℝ)^3611 := by
    have hnat : (5440283737 : ℕ)^4635*50000000000000^3611 ≤ 22888622418621^3611*10000000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5440283737 10000000000 22888622418621 50000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4635/1024 : ℝ)) 4635 3611 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1058002859/2000000000 : ℝ), (-1671179349/10000000000 : ℝ), (5440283737/10000000000 : ℝ)] ![(44160634334301/100000000000000 : ℝ), (10062120820093/100000000000000 : ℝ), (22888622418621/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1058002859/2000000000 : ℝ)|^4635 ≤ (44160634334301/100000000000000 : ℝ)^3611
        have hw : |(1058002859/2000000000 : ℝ)|=(1058002859/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1671179349/10000000000 : ℝ)|^4635 ≤ (10062120820093/100000000000000 : ℝ)^3611
        have hw : |(-1671179349/10000000000 : ℝ)|=(1671179349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5440283737/10000000000 : ℝ)|^4635 ≤ (22888622418621/50000000000000 : ℝ)^3611
        have hw : |(5440283737/10000000000 : ℝ)|=(5440283737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1569_s2_6 (p : ℝ) (hpa : (4633/1024 : ℝ) ≤ p) (hpb : p ≤ (4635/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (661251833/1250000000 : ℝ)*x 0 + (5440283439/10000000000 : ℝ)*x 1 + (-1671179253/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (661251833/1250000000 : ℝ)^4635 ≤ (44160638288213/100000000000000 : ℝ)^3611 := by
    have hnat : (661251833 : ℕ)^4635*100000000000000^3611 ≤ 44160638288213^3611*1250000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      661251833 1250000000 44160638288213 100000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5440283439/10000000000 : ℝ)^4635 ≤ (9155448323729/20000000000000 : ℝ)^3611 := by
    have hnat : (5440283439 : ℕ)^4635*20000000000000^3611 ≤ 9155448323729^3611*10000000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5440283439 10000000000 9155448323729 20000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1671179253/10000000000 : ℝ)^4635 ≤ (1257765009771/12500000000000 : ℝ)^3611 := by
    have hnat : (1671179253 : ℕ)^4635*12500000000000^3611 ≤ 1257765009771^3611*10000000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1671179253 10000000000 1257765009771 12500000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4635/1024 : ℝ)) 4635 3611 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(661251833/1250000000 : ℝ), (5440283439/10000000000 : ℝ), (-1671179253/10000000000 : ℝ)] ![(44160638288213/100000000000000 : ℝ), (9155448323729/20000000000000 : ℝ), (1257765009771/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(661251833/1250000000 : ℝ)|^4635 ≤ (44160638288213/100000000000000 : ℝ)^3611
        have hw : |(661251833/1250000000 : ℝ)|=(661251833/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5440283439/10000000000 : ℝ)|^4635 ≤ (9155448323729/20000000000000 : ℝ)^3611
        have hw : |(5440283439/10000000000 : ℝ)|=(5440283439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1671179253/10000000000 : ℝ)|^4635 ≤ (1257765009771/12500000000000 : ℝ)^3611
        have hw : |(-1671179253/10000000000 : ℝ)|=(1671179253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1569_s2_7 (p : ℝ) (hpa : (4633/1024 : ℝ) ≤ p) (hpb : p ≤ (4635/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (84849209/200000000 : ℝ)*x 0 + (4524623123/10000000000 : ℝ)*x 1 + (198745523/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (84849209/200000000 : ℝ)^4635 ≤ (33267366271699/100000000000000 : ℝ)^3611 := by
    have hnat : (84849209 : ℕ)^4635*100000000000000^3611 ≤ 33267366271699^3611*200000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84849209 200000000 33267366271699 100000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4524623123/10000000000 : ℝ)^4635 ≤ (3613376157169/10000000000000 : ℝ)^3611 := by
    have hnat : (4524623123 : ℕ)^4635*10000000000000^3611 ≤ 3613376157169^3611*10000000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4524623123 10000000000 3613376157169 10000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (198745523/500000000 : ℝ)^4635 ≤ (15299436069193/50000000000000 : ℝ)^3611 := by
    have hnat : (198745523 : ℕ)^4635*50000000000000^3611 ≤ 15299436069193^3611*500000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      198745523 500000000 15299436069193 50000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4635/1024 : ℝ)) 4635 3611 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(84849209/200000000 : ℝ), (4524623123/10000000000 : ℝ), (198745523/500000000 : ℝ)] ![(33267366271699/100000000000000 : ℝ), (3613376157169/10000000000000 : ℝ), (15299436069193/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(84849209/200000000 : ℝ)|^4635 ≤ (33267366271699/100000000000000 : ℝ)^3611
        have hw : |(84849209/200000000 : ℝ)|=(84849209/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4524623123/10000000000 : ℝ)|^4635 ≤ (3613376157169/10000000000000 : ℝ)^3611
        have hw : |(4524623123/10000000000 : ℝ)|=(4524623123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(198745523/500000000 : ℝ)|^4635 ≤ (15299436069193/50000000000000 : ℝ)^3611
        have hw : |(198745523/500000000 : ℝ)|=(198745523/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1569_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4633/1024 : ℝ) ≤ p) (hpb : p ≤ (4635/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (167947699/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4441/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4529/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (5407/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7907/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4441/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4529/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4441/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4529/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4441/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4529/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4441/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4529/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4441/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4529/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4441/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4529/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (4529/50000 : ℝ) ^ (4633/1024 : ℝ) ≤ (1910655308764159/100000000000000000000 : ℝ) := by
    have hpowers : (4529/50000 : ℝ)^4633 ≤ (1910655308764159/100000000000000000000 : ℝ)^1024 := by
      have hnat : (4529 : ℕ)^4633*100000000000000000000^1024 ≤ 1910655308764159^1024*50000^4633 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4529 50000 1910655308764159 100000000000000000000 4633 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4529/50000 : ℝ)) (X := (1910655308764159/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4633 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (4441/25000 : ℝ) ^ (4633/1024 : ℝ) ≤ (40235711137699989/100000000000000000000 : ℝ) := by
    have hpowers : (4441/25000 : ℝ)^4633 ≤ (40235711137699989/100000000000000000000 : ℝ)^1024 := by
      have hnat : (4441 : ℕ)^4633*100000000000000000000^1024 ≤ 40235711137699989^1024*25000^4633 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4441 25000 40235711137699989 100000000000000000000 4633 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4441/25000 : ℝ)) (X := (40235711137699989/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4633 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001910655308764159/50000000000000000000 : ℝ) ≤ (5000042229266501/5000000000000000 : ℝ) ^ (4633/1024 : ℝ) := by
    have hpowers : (50001910655308764159/50000000000000000000 : ℝ)^1024 ≤ (5000042229266501/5000000000000000 : ℝ)^4633 := by
      have hnat : (50001910655308764159 : ℕ)^1024*5000000000000000^4633 ≤ 5000042229266501^4633*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001910655308764159 50000000000000000000 5000042229266501 5000000000000000 1024 4633 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000042229266501/5000000000000000 : ℝ)) (X := (50001910655308764159/50000000000000000000 : ℝ)) (by norm_num) 4633 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25010536591611616037/25000000000000000000 : ℝ) ≤ (5000465689579319/5000000000000000 : ℝ) ^ (4633/1024 : ℝ) := by
    have hpowers : (25010536591611616037/25000000000000000000 : ℝ)^1024 ≤ (5000465689579319/5000000000000000 : ℝ)^4633 := by
      have hnat : (25010536591611616037 : ℕ)^1024*5000000000000000^4633 ≤ 5000465689579319^4633*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25010536591611616037 25000000000000000000 5000465689579319 5000000000000000 1024 4633 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000465689579319/5000000000000000 : ℝ)) (X := (25010536591611616037/25000000000000000000 : ℝ)) (by norm_num) 4633 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50040235711137699989/50000000000000000000 : ℝ) ≤ (5000889149892137/5000000000000000 : ℝ) ^ (4633/1024 : ℝ) := by
    have hpowers : (50040235711137699989/50000000000000000000 : ℝ)^1024 ≤ (5000889149892137/5000000000000000 : ℝ)^4633 := by
      have hnat : (50040235711137699989 : ℕ)^1024*5000000000000000^4633 ≤ 5000889149892137^4633*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50040235711137699989 50000000000000000000 5000889149892137 5000000000000000 1024 4633 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000889149892137/5000000000000000 : ℝ)) (X := (50040235711137699989/50000000000000000000 : ℝ)) (by norm_num) 4633 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1910655308764159/100000000000000000000 : ℝ) ≤ ((7253782706827857803/7255000000000000000 : ℝ)+2*(70576718803/72550000000000 : ℝ)*(4529/50000 : ℝ))^(4633/1024 : ℝ) := by
    rw [show (7253782706827857803/7255000000000000000 : ℝ)+2*(70576718803/72550000000000 : ℝ)*(4529/50000 : ℝ)=(5000042229266501/5000000000000000 : ℝ) by norm_num, show 1+2*(1910655308764159/100000000000000000000 : ℝ)=(50001910655308764159/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(40235711137699989/100000000000000000000 : ℝ)+(1910655308764159/100000000000000000000 : ℝ) ≤ ((7253782706827857803/7255000000000000000 : ℝ)+(70576718803/72550000000000 : ℝ)*((4441/25000 : ℝ)+(4529/50000 : ℝ)))^(4633/1024 : ℝ) := by
    rw [show (7253782706827857803/7255000000000000000 : ℝ)+(70576718803/72550000000000 : ℝ)*((4441/25000 : ℝ)+(4529/50000 : ℝ))=(5000465689579319/5000000000000000 : ℝ) by norm_num, show 1+(40235711137699989/100000000000000000000 : ℝ)+(1910655308764159/100000000000000000000 : ℝ)=(25010536591611616037/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(40235711137699989/100000000000000000000 : ℝ) ≤ ((7253782706827857803/7255000000000000000 : ℝ)+2*(70576718803/72550000000000 : ℝ)*(4441/25000 : ℝ))^(4633/1024 : ℝ) := by
    rw [show (7253782706827857803/7255000000000000000 : ℝ)+2*(70576718803/72550000000000 : ℝ)*(4441/25000 : ℝ)=(5000889149892137/5000000000000000 : ℝ) by norm_num, show 1+2*(40235711137699989/100000000000000000000 : ℝ)=(50040235711137699989/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (7253782706827857803/7255000000000000000 : ℝ)*(X 1 0+X 2 0)+(70576718803/72550000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4633/1024 : ℝ)) (lo := (4529/50000 : ℝ)) (hi := (4441/25000 : ℝ)) (c := (7253782706827857803/7255000000000000000 : ℝ)) (alpha := (70576718803/72550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (7253782706827857803/7255000000000000000 : ℝ)*(X 0 1+X 2 1)+(70576718803/72550000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4633/1024 : ℝ)) (lo := (4529/50000 : ℝ)) (hi := (4441/25000 : ℝ)) (c := (7253782706827857803/7255000000000000000 : ℝ)) (alpha := (70576718803/72550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (7253782706827857803/7255000000000000000 : ℝ)*(X 0 2+X 1 2)+(70576718803/72550000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4633/1024 : ℝ)) (lo := (4529/50000 : ℝ)) (hi := (4441/25000 : ℝ)) (c := (7253782706827857803/7255000000000000000 : ℝ)) (alpha := (70576718803/72550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-892278797/5000000000 : ℝ)*X 0 0+(2720850499/5000000000 : ℝ)*X 0 1+(1301461591/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1569_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5352412599/10000000000 : ℝ)*X 1 0+(-190561681/1000000000 : ℝ)*X 1 1+(5205846169/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1569_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5352412591/10000000000 : ℝ)*X 2 0+(5205846097/10000000000 : ℝ)*X 2 1+(-476404229/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1569_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4242365391/10000000000 : ℝ)*X 0 0+(794313471/2000000000 : ℝ)*X 0 1+(2263969133/5000000000 : ℝ)*X 0 2+(4242365391/10000000000 : ℝ)*X 1 0+(794313471/2000000000 : ℝ)*X 1 1+(2263969133/5000000000 : ℝ)*X 1 2+(4242365391/10000000000 : ℝ)*X 2 0+(794313471/2000000000 : ℝ)*X 2 1+(2263969133/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1569_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-111537371/625000000 : ℝ)*X 0 0+(1301812903/2500000000 : ℝ)*X 0 1+(1088056757/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1569_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1058002859/2000000000 : ℝ)*X 1 0+(-1671179349/10000000000 : ℝ)*X 1 1+(5440283737/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1569_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((661251833/1250000000 : ℝ)*X 2 0+(5440283439/10000000000 : ℝ)*X 2 1+(-1671179253/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1569_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((84849209/200000000 : ℝ)*X 0 0+(4524623123/10000000000 : ℝ)*X 0 1+(198745523/500000000 : ℝ)*X 0 2+(84849209/200000000 : ℝ)*X 1 0+(4524623123/10000000000 : ℝ)*X 1 1+(198745523/500000000 : ℝ)*X 1 2+(84849209/200000000 : ℝ)*X 2 0+(4524623123/10000000000 : ℝ)*X 2 1+(198745523/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1569_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1435070356103330586120599631/181375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1432609861/100000000000000 : ℝ)*(base19) + (158415623/12500000000000 : ℝ)*(base23) + (85075341/100000000000000 : ℝ)*(lower2) + (55174863/20000000000000 : ℝ)*(upper3) + (58813999/100000000000000 : ℝ)*(upper5) + (1509327638003441/50000000000000 : ℝ)*(major0) + (1509327638003441/50000000000000 : ℝ)*(major1) + (1509327638003441/50000000000000 : ℝ)*(major2) + (211995905891911/5000000000000 : ℝ)*(sp0) + (2119965343676837/50000000000000 : ℝ)*(sp1) + (4239930852638551/100000000000000 : ℝ)*(sp2) + (1797368824428023/100000000000000 : ℝ)*(sp3) + (3500531329/25000000000000 : ℝ)*(sp4) + (4671941551/50000000000000 : ℝ)*(sp7) + (898689084155563/50000000000000 : ℝ)*(f.failure) + (847986423992707/20000000000000 : ℝ)*(f.sum) + (30260838799057/7255000000000000000000000000 : ℝ)*base65 + (2155062736168249877/362750000000000000000000000000000 : ℝ)*base68 + (3486499797484499877/362750000000000000000000000000000 : ℝ)*base70 + (520908843042750123/362750000000000000000000000000000 : ℝ)*base71 + (29318999530887/7255000000000000000000000000 : ℝ)*base73 + (1141848576899000123/362750000000000000000000000000000 : ℝ)*base75 + (64621247126500123/362750000000000000000000000000000 : ℝ)*base77 + (2803173851270500123/362750000000000000000000000000000 : ℝ)*base79 + (3549278980809/3627500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (63899537/5000000000000000000000 : ℝ)*base89 + (63899537/5000000000000000000000 : ℝ)*base91 + (63899537/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (157381470772324873606849581/45343750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (672128719/100000000000000 : ℝ)*(base19) + (44313659/4000000000000 : ℝ)*(base23) + (140633027/100000000000000 : ℝ)*(upper3) + (2488457/6250000000000 : ℝ)*(lower4) + (4097173/6250000000000 : ℝ)*(upper5) + (763798179802891/25000000000000 : ℝ)*(major0) + (763798179802891/25000000000000 : ℝ)*(major1) + (763798179802891/25000000000000 : ℝ)*(major2) + (1239055591/20000000000000 : ℝ)*(sp1) + (355519059/3125000000000 : ℝ)*(sp2) + (1072812975893151/25000000000000 : ℝ)*(sp4) + (429124503616593/10000000000000 : ℝ)*(sp5) + (107280985478031/2500000000000 : ℝ)*(sp6) + (909566709577713/50000000000000 : ℝ)*(sp7) + (909566709577713/50000000000000 : ℝ)*(f.failure) + (1072812975893151/25000000000000 : ℝ)*(f.sum) + (4478290671749/1813750000000000000000000000 : ℝ)*base66 + (2508311453545358473/181375000000000000000000000000000 : ℝ)*base67 + (1631684533876108473/181375000000000000000000000000000 : ℝ)*base69 + (459540920717016527/181375000000000000000000000000000 : ℝ)*base72 + (25492495049447/3627500000000000000000000000 : ℝ)*base73 + (2968788531011733473/181375000000000000000000000000000 : ℝ)*base75 + (1956512146830108473/181375000000000000000000000000000 : ℝ)*base77 + (1836586629364358473/181375000000000000000000000000000 : ℝ)*base79 + (4104898294953/906875000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (39967613/5000000000000000000000 : ℝ)*base90 + (39967613/5000000000000000000000 : ℝ)*base92 + (39967613/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1569_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4633/1024 : ℝ) ≤ p) (hpb : p ≤ (4635/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (167947699/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4441/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4529/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5407/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7907/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1569_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1569_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4633/1024 : ℝ) ≤ p) (hpb : p ≤ (4635/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (167947699/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5407/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7907/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1569_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1569_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1569_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4633/1024 : ℝ) ≤ p) (hpb : p ≤ (4635/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (167947699/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5407/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7907/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1569_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
