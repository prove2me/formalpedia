-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1763_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:29:13.158908+00:00
-- url     : https://prove2.me/submissions/a895e51b-f3f3-4539-afb8-6fdf8365e9ff

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
theorem support_rectangle_w1763_s0_0 (p : ℝ) (hpa : (5967/1024 : ℝ) ≤ p) (hpb : p ≤ (5983/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1117533239/10000000000 : ℝ)*x 0 + (2796261717/5000000000 : ℝ)*x 1 + (4996094687/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1117533239/10000000000 : ℝ)^5983 ≤ (710775846849/10000000000000 : ℝ)^4959 := by
    have hnat : (1117533239 : ℕ)^5983*10000000000000^4959 ≤ 710775846849^4959*10000000000^5983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1117533239 10000000000 710775846849 10000000000000 5983 4959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2796261717/5000000000 : ℝ)^5983 ≤ (24800505626847/50000000000000 : ℝ)^4959 := by
    have hnat : (2796261717 : ℕ)^5983*50000000000000^4959 ≤ 24800505626847^4959*5000000000^5983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2796261717 5000000000 24800505626847 50000000000000 5983 4959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4996094687/10000000000 : ℝ)^5983 ≤ (8658246052713/20000000000000 : ℝ)^4959 := by
    have hnat : (4996094687 : ℕ)^5983*20000000000000^4959 ≤ 8658246052713^4959*10000000000^5983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4996094687 10000000000 8658246052713 20000000000000 5983 4959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5983/1024 : ℝ)) 5983 4959 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1117533239/10000000000 : ℝ), (2796261717/5000000000 : ℝ), (4996094687/10000000000 : ℝ)] ![(710775846849/10000000000000 : ℝ), (24800505626847/50000000000000 : ℝ), (8658246052713/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1117533239/10000000000 : ℝ)|^5983 ≤ (710775846849/10000000000000 : ℝ)^4959
        have hw : |(-1117533239/10000000000 : ℝ)|=(1117533239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2796261717/5000000000 : ℝ)|^5983 ≤ (24800505626847/50000000000000 : ℝ)^4959
        have hw : |(2796261717/5000000000 : ℝ)|=(2796261717/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4996094687/10000000000 : ℝ)|^5983 ≤ (8658246052713/20000000000000 : ℝ)^4959
        have hw : |(4996094687/10000000000 : ℝ)|=(4996094687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1763_s0_1 (p : ℝ) (hpa : (5967/1024 : ℝ) ≤ p) (hpb : p ≤ (5983/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5357143651/10000000000 : ℝ)*x 0 + (-28711991/200000000 : ℝ)*x 1 + (2498047949/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5357143651/10000000000 : ℝ)^5983 ≤ (23546689250253/50000000000000 : ℝ)^4959 := by
    have hnat : (5357143651 : ℕ)^5983*50000000000000^4959 ≤ 23546689250253^4959*10000000000^5983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5357143651 10000000000 23546689250253 50000000000000 5983 4959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (28711991/200000000 : ℝ)^5983 ≤ (9615378563193/100000000000000 : ℝ)^4959 := by
    have hnat : (28711991 : ℕ)^5983*100000000000000^4959 ≤ 9615378563193^4959*200000000^5983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      28711991 200000000 9615378563193 100000000000000 5983 4959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2498047949/5000000000 : ℝ)^5983 ≤ (43291242923699/100000000000000 : ℝ)^4959 := by
    have hnat : (2498047949 : ℕ)^5983*100000000000000^4959 ≤ 43291242923699^4959*5000000000^5983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2498047949 5000000000 43291242923699 100000000000000 5983 4959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5983/1024 : ℝ)) 5983 4959 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5357143651/10000000000 : ℝ), (-28711991/200000000 : ℝ), (2498047949/5000000000 : ℝ)] ![(23546689250253/50000000000000 : ℝ), (9615378563193/100000000000000 : ℝ), (43291242923699/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5357143651/10000000000 : ℝ)|^5983 ≤ (23546689250253/50000000000000 : ℝ)^4959
        have hw : |(5357143651/10000000000 : ℝ)|=(5357143651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-28711991/200000000 : ℝ)|^5983 ≤ (9615378563193/100000000000000 : ℝ)^4959
        have hw : |(-28711991/200000000 : ℝ)|=(28711991/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2498047949/5000000000 : ℝ)|^5983 ≤ (43291242923699/100000000000000 : ℝ)^4959
        have hw : |(2498047949/5000000000 : ℝ)|=(2498047949/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1763_s0_2 (p : ℝ) (hpa : (5967/1024 : ℝ) ≤ p) (hpb : p ≤ (5983/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5357147657/10000000000 : ℝ)*x 0 + (4996093139/10000000000 : ℝ)*x 1 + (-717798931/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5357147657/10000000000 : ℝ)^5983 ≤ (1471669405879/3125000000000 : ℝ)^4959 := by
    have hnat : (5357147657 : ℕ)^5983*3125000000000^4959 ≤ 1471669405879^4959*10000000000^5983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5357147657 10000000000 1471669405879 3125000000000 5983 4959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4996093139/10000000000 : ℝ)^5983 ≤ (43291214080339/100000000000000 : ℝ)^4959 := by
    have hnat : (4996093139 : ℕ)^5983*100000000000000^4959 ≤ 43291214080339^4959*10000000000^5983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4996093139 10000000000 43291214080339 100000000000000 5983 4959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (717798931/5000000000 : ℝ)^5983 ≤ (9615364922691/100000000000000 : ℝ)^4959 := by
    have hnat : (717798931 : ℕ)^5983*100000000000000^4959 ≤ 9615364922691^4959*5000000000^5983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      717798931 5000000000 9615364922691 100000000000000 5983 4959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5983/1024 : ℝ)) 5983 4959 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5357147657/10000000000 : ℝ), (4996093139/10000000000 : ℝ), (-717798931/5000000000 : ℝ)] ![(1471669405879/3125000000000 : ℝ), (43291214080339/100000000000000 : ℝ), (9615364922691/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5357147657/10000000000 : ℝ)|^5983 ≤ (1471669405879/3125000000000 : ℝ)^4959
        have hw : |(5357147657/10000000000 : ℝ)|=(5357147657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4996093139/10000000000 : ℝ)|^5983 ≤ (43291214080339/100000000000000 : ℝ)^4959
        have hw : |(4996093139/10000000000 : ℝ)|=(4996093139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-717798931/5000000000 : ℝ)|^5983 ≤ (9615364922691/100000000000000 : ℝ)^4959
        have hw : |(-717798931/5000000000 : ℝ)|=(717798931/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1763_s0_3 (p : ℝ) (hpa : (5967/1024 : ℝ) ≤ p) (hpb : p ≤ (5983/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (3958712971/10000000000 : ℝ)*x 0 + (2995478361/10000000000 : ℝ)*x 1 + (1264835703/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3958712971/10000000000 : ℝ)^5983 ≤ (16346381896801/50000000000000 : ℝ)^4959 := by
    have hnat : (3958712971 : ℕ)^5983*50000000000000^4959 ≤ 16346381896801^4959*10000000000^5983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3958712971 10000000000 16346381896801 50000000000000 5983 4959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2995478361/10000000000 : ℝ)^5983 ≤ (23353930899239/100000000000000 : ℝ)^4959 := by
    have hnat : (2995478361 : ℕ)^5983*100000000000000^4959 ≤ 23353930899239^4959*10000000000^5983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2995478361 10000000000 23353930899239 100000000000000 5983 4959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1264835703/2500000000 : ℝ)^5983 ≤ (5494163160839/12500000000000 : ℝ)^4959 := by
    have hnat : (1264835703 : ℕ)^5983*12500000000000^4959 ≤ 5494163160839^4959*2500000000^5983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1264835703 2500000000 5494163160839 12500000000000 5983 4959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5983/1024 : ℝ)) 5983 4959 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3958712971/10000000000 : ℝ), (2995478361/10000000000 : ℝ), (1264835703/2500000000 : ℝ)] ![(16346381896801/50000000000000 : ℝ), (23353930899239/100000000000000 : ℝ), (5494163160839/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3958712971/10000000000 : ℝ)|^5983 ≤ (16346381896801/50000000000000 : ℝ)^4959
        have hw : |(3958712971/10000000000 : ℝ)|=(3958712971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2995478361/10000000000 : ℝ)|^5983 ≤ (23353930899239/100000000000000 : ℝ)^4959
        have hw : |(2995478361/10000000000 : ℝ)|=(2995478361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1264835703/2500000000 : ℝ)|^5983 ≤ (5494163160839/12500000000000 : ℝ)^4959
        have hw : |(1264835703/2500000000 : ℝ)|=(1264835703/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1763_s0_4 (p : ℝ) (hpa : (5967/1024 : ℝ) ≤ p) (hpb : p ≤ (5983/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-559326133/5000000000 : ℝ)*x 0 + (5010980639/10000000000 : ℝ)*x 1 + (2788584373/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (559326133/5000000000 : ℝ)^5983 ≤ (7116346281057/100000000000000 : ℝ)^4959 := by
    have hnat : (559326133 : ℕ)^5983*100000000000000^4959 ≤ 7116346281057^4959*5000000000^5983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      559326133 5000000000 7116346281057 100000000000000 5983 4959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5010980639/10000000000 : ℝ)^5983 ≤ (43446900021589/100000000000000 : ℝ)^4959 := by
    have hnat : (5010980639 : ℕ)^5983*100000000000000^4959 ≤ 43446900021589^4959*10000000000^5983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5010980639 10000000000 43446900021589 100000000000000 5983 4959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2788584373/5000000000 : ℝ)^5983 ≤ (24718376842147/50000000000000 : ℝ)^4959 := by
    have hnat : (2788584373 : ℕ)^5983*50000000000000^4959 ≤ 24718376842147^4959*5000000000^5983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2788584373 5000000000 24718376842147 50000000000000 5983 4959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5983/1024 : ℝ)) 5983 4959 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-559326133/5000000000 : ℝ), (5010980639/10000000000 : ℝ), (2788584373/5000000000 : ℝ)] ![(7116346281057/100000000000000 : ℝ), (43446900021589/100000000000000 : ℝ), (24718376842147/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-559326133/5000000000 : ℝ)|^5983 ≤ (7116346281057/100000000000000 : ℝ)^4959
        have hw : |(-559326133/5000000000 : ℝ)|=(559326133/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5010980639/10000000000 : ℝ)|^5983 ≤ (43446900021589/100000000000000 : ℝ)^4959
        have hw : |(5010980639/10000000000 : ℝ)|=(5010980639/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2788584373/5000000000 : ℝ)|^5983 ≤ (24718376842147/50000000000000 : ℝ)^4959
        have hw : |(2788584373/5000000000 : ℝ)|=(2788584373/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1763_s0_5 (p : ℝ) (hpa : (5967/1024 : ℝ) ≤ p) (hpb : p ≤ (5983/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1039799499/2000000000 : ℝ)*x 0 + (-854524997/10000000000 : ℝ)*x 1 + (1394292181/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1039799499/2000000000 : ℝ)^5983 ≤ (45421233730913/100000000000000 : ℝ)^4959 := by
    have hnat : (1039799499 : ℕ)^5983*100000000000000^4959 ≤ 45421233730913^4959*2000000000^5983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1039799499 2000000000 45421233730913 100000000000000 5983 4959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (854524997/10000000000 : ℝ)^5983 ≤ (5142012799683/100000000000000 : ℝ)^4959 := by
    have hnat : (854524997 : ℕ)^5983*100000000000000^4959 ≤ 5142012799683^4959*10000000000^5983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      854524997 10000000000 5142012799683 100000000000000 5983 4959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1394292181/2500000000 : ℝ)^5983 ≤ (9887350689803/20000000000000 : ℝ)^4959 := by
    have hnat : (1394292181 : ℕ)^5983*20000000000000^4959 ≤ 9887350689803^4959*2500000000^5983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1394292181 2500000000 9887350689803 20000000000000 5983 4959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5983/1024 : ℝ)) 5983 4959 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1039799499/2000000000 : ℝ), (-854524997/10000000000 : ℝ), (1394292181/2500000000 : ℝ)] ![(45421233730913/100000000000000 : ℝ), (5142012799683/100000000000000 : ℝ), (9887350689803/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1039799499/2000000000 : ℝ)|^5983 ≤ (45421233730913/100000000000000 : ℝ)^4959
        have hw : |(1039799499/2000000000 : ℝ)|=(1039799499/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-854524997/10000000000 : ℝ)|^5983 ≤ (5142012799683/100000000000000 : ℝ)^4959
        have hw : |(-854524997/10000000000 : ℝ)|=(854524997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1394292181/2500000000 : ℝ)|^5983 ≤ (9887350689803/20000000000000 : ℝ)^4959
        have hw : |(1394292181/2500000000 : ℝ)|=(1394292181/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1763_s0_6 (p : ℝ) (hpa : (5967/1024 : ℝ) ≤ p) (hpb : p ≤ (5983/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5198997733/10000000000 : ℝ)*x 0 + (892347/1600000 : ℝ)*x 1 + (-427262307/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5198997733/10000000000 : ℝ)^5983 ≤ (45421236239569/100000000000000 : ℝ)^4959 := by
    have hnat : (5198997733 : ℕ)^5983*100000000000000^4959 ≤ 45421236239569^4959*10000000000^5983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5198997733 10000000000 45421236239569 100000000000000 5983 4959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (892347/1600000 : ℝ)^5983 ≤ (1544898553971/3125000000000 : ℝ)^4959 := by
    have hnat : (892347 : ℕ)^5983*3125000000000^4959 ≤ 1544898553971^4959*1600000^5983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      892347 1600000 1544898553971 3125000000000 5983 4959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (427262307/5000000000 : ℝ)^5983 ≤ (41136080153/800000000000 : ℝ)^4959 := by
    have hnat : (427262307 : ℕ)^5983*800000000000^4959 ≤ 41136080153^4959*5000000000^5983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      427262307 5000000000 41136080153 800000000000 5983 4959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5983/1024 : ℝ)) 5983 4959 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5198997733/10000000000 : ℝ), (892347/1600000 : ℝ), (-427262307/5000000000 : ℝ)] ![(45421236239569/100000000000000 : ℝ), (1544898553971/3125000000000 : ℝ), (41136080153/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5198997733/10000000000 : ℝ)|^5983 ≤ (45421236239569/100000000000000 : ℝ)^4959
        have hw : |(5198997733/10000000000 : ℝ)|=(5198997733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(892347/1600000 : ℝ)|^5983 ≤ (1544898553971/3125000000000 : ℝ)^4959
        have hw : |(892347/1600000 : ℝ)|=(892347/1600000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-427262307/5000000000 : ℝ)|^5983 ≤ (41136080153/800000000000 : ℝ)^4959
        have hw : |(-427262307/5000000000 : ℝ)|=(427262307/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1763_s0_7 (p : ℝ) (hpa : (5967/1024 : ℝ) ≤ p) (hpb : p ≤ (5983/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (3962591257/10000000000 : ℝ)*x 0 + (5007829057/10000000000 : ℝ)*x 1 + (121944577/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3962591257/10000000000 : ℝ)^5983 ≤ (32731409946209/100000000000000 : ℝ)^4959 := by
    have hnat : (3962591257 : ℕ)^5983*100000000000000^4959 ≤ 32731409946209^4959*10000000000^5983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3962591257 10000000000 32731409946209 100000000000000 5983 4959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5007829057/10000000000 : ℝ)^5983 ≤ (43413934392413/100000000000000 : ℝ)^4959 := by
    have hnat : (5007829057 : ℕ)^5983*100000000000000^4959 ≤ 43413934392413^4959*10000000000^5983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5007829057 10000000000 43413934392413 100000000000000 5983 4959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (121944577/400000000 : ℝ)^5983 ≤ (2981831955341/12500000000000 : ℝ)^4959 := by
    have hnat : (121944577 : ℕ)^5983*12500000000000^4959 ≤ 2981831955341^4959*400000000^5983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      121944577 400000000 2981831955341 12500000000000 5983 4959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5983/1024 : ℝ)) 5983 4959 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3962591257/10000000000 : ℝ), (5007829057/10000000000 : ℝ), (121944577/400000000 : ℝ)] ![(32731409946209/100000000000000 : ℝ), (43413934392413/100000000000000 : ℝ), (2981831955341/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3962591257/10000000000 : ℝ)|^5983 ≤ (32731409946209/100000000000000 : ℝ)^4959
        have hw : |(3962591257/10000000000 : ℝ)|=(3962591257/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5007829057/10000000000 : ℝ)|^5983 ≤ (43413934392413/100000000000000 : ℝ)^4959
        have hw : |(5007829057/10000000000 : ℝ)|=(5007829057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(121944577/400000000 : ℝ)|^5983 ≤ (2981831955341/12500000000000 : ℝ)^4959
        have hw : |(121944577/400000000 : ℝ)|=(121944577/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1763_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5967/1024 : ℝ) ≤ p) (hpb : p ≤ (5983/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (111508997/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (3603/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (20143/100000 : ℝ)*pair X 0 0 := by
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
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base24 : ((-1 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 2).1]
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
  have hpowlo : (0 : ℝ) ^ (5967/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^5967 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^5967*1^1024 ≤ 0^1024*1^5967 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 5967 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 5967 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (5967/1024 : ℝ) ≤ (479893094082243637/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^5967 ≤ (479893094082243637/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^5967*100000000000000000000^1024 ≤ 479893094082243637^1024*5^5967 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 479893094082243637 100000000000000000000 5967 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (479893094082243637/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5967 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (5967/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^5967 := by
      have hnat : (1 : ℕ)^1024*1^5967 ≤ 1^5967*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 5967 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 5967 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100479893094082243637/100000000000000000000 : ℝ) ≤ (2502054787174339/2500000000000000 : ℝ) ^ (5967/1024 : ℝ) := by
    have hpowers : (100479893094082243637/100000000000000000000 : ℝ)^1024 ≤ (2502054787174339/2500000000000000 : ℝ)^5967 := by
      have hnat : (100479893094082243637 : ℕ)^1024*2500000000000000^5967 ≤ 2502054787174339^5967*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100479893094082243637 100000000000000000000 2502054787174339 2500000000000000 1024 5967 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2502054787174339/2500000000000000 : ℝ)) (X := (100479893094082243637/100000000000000000000 : ℝ)) (by norm_num) 5967 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50479893094082243637/50000000000000000000 : ℝ) ≤ (1252054787174339/1250000000000000 : ℝ) ^ (5967/1024 : ℝ) := by
    have hpowers : (50479893094082243637/50000000000000000000 : ℝ)^1024 ≤ (1252054787174339/1250000000000000 : ℝ)^5967 := by
      have hnat : (50479893094082243637 : ℕ)^1024*1250000000000000^5967 ≤ 1252054787174339^5967*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50479893094082243637 50000000000000000000 1252054787174339 1250000000000000 1024 5967 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1252054787174339/1250000000000000 : ℝ)) (X := (50479893094082243637/50000000000000000000 : ℝ)) (by norm_num) 5967 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(2054787174339/1000000000000000 : ℝ)*(0 : ℝ))^(5967/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(2054787174339/1000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(479893094082243637/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(2054787174339/1000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(5967/1024 : ℝ) := by
    rw [show (1 : ℝ)+(2054787174339/1000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(2502054787174339/2500000000000000 : ℝ) by norm_num, show 1+(479893094082243637/100000000000000000000 : ℝ)+(0 : ℝ)=(100479893094082243637/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(479893094082243637/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(2054787174339/1000000000000000 : ℝ)*(2/5 : ℝ))^(5967/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(2054787174339/1000000000000000 : ℝ)*(2/5 : ℝ)=(1252054787174339/1250000000000000 : ℝ) by norm_num, show 1+2*(479893094082243637/100000000000000000000 : ℝ)=(50479893094082243637/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(2054787174339/1000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5967/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (2054787174339/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(2054787174339/1000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5967/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (2054787174339/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(2054787174339/1000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5967/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (2054787174339/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1117533239/10000000000 : ℝ)*X 0 0+(2796261717/5000000000 : ℝ)*X 0 1+(4996094687/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1763_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5357143651/10000000000 : ℝ)*X 1 0+(-28711991/200000000 : ℝ)*X 1 1+(2498047949/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1763_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5357147657/10000000000 : ℝ)*X 2 0+(4996093139/10000000000 : ℝ)*X 2 1+(-717798931/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1763_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((3958712971/10000000000 : ℝ)*X 0 0+(2995478361/10000000000 : ℝ)*X 0 1+(1264835703/2500000000 : ℝ)*X 0 2+(3958712971/10000000000 : ℝ)*X 1 0+(2995478361/10000000000 : ℝ)*X 1 1+(1264835703/2500000000 : ℝ)*X 1 2+(3958712971/10000000000 : ℝ)*X 2 0+(2995478361/10000000000 : ℝ)*X 2 1+(1264835703/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1763_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-559326133/5000000000 : ℝ)*X 0 0+(5010980639/10000000000 : ℝ)*X 0 1+(2788584373/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1763_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1039799499/2000000000 : ℝ)*X 1 0+(-854524997/10000000000 : ℝ)*X 1 1+(1394292181/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1763_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5198997733/10000000000 : ℝ)*X 2 0+(892347/1600000 : ℝ)*X 2 1+(-427262307/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1763_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((3962591257/10000000000 : ℝ)*X 0 0+(5007829057/10000000000 : ℝ)*X 0 1+(121944577/400000000 : ℝ)*X 0 2+(3962591257/10000000000 : ℝ)*X 1 0+(5007829057/10000000000 : ℝ)*X 1 1+(121944577/400000000 : ℝ)*X 1 2+(3962591257/10000000000 : ℝ)*X 2 0+(5007829057/10000000000 : ℝ)*X 2 1+(121944577/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1763_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (12233681953439339758797/1562500000000000000000000000 : ℝ) := by norm_num
    linear_combination (334382607/25000000000000 : ℝ)*(base19) + (529699359/25000000000000 : ℝ)*(base23) + (63249849/100000000000000 : ℝ)*(base24) + (219251173/100000000000000 : ℝ)*(upper4) + (2712143/500000000000 : ℝ)*(upper5) + (33768746082159/3125000000000 : ℝ)*(major0) + (33768746082159/3125000000000 : ℝ)*(major1) + (33768746082159/3125000000000 : ℝ)*(major2) + (1676649638462473/100000000000000 : ℝ)*(sp0) + (167666331332977/10000000000000 : ℝ)*(sp1) + (838331234406457/50000000000000 : ℝ)*(sp2) + (484531801922581/100000000000000 : ℝ)*(sp3) + (7506198863/50000000000000 : ℝ)*(sp4) + (1517745087/50000000000000 : ℝ)*(sp7) + (96906967482551/20000000000000 : ℝ)*(f.failure) + (838332325430099/50000000000000 : ℝ)*(f.sum) + (2343056494319/390625000000000000000000000 : ℝ)*base65 + (2030941701987/1562500000000000000000000000 : ℝ)*base68 + (6034357893181/781250000000000000000000000 : ℝ)*base70 + (3819960979263/1562500000000000000000000000 : ℝ)*base71 + (16448100538927/3125000000000000000000000000 : ℝ)*base73 + (25529403175849/3125000000000000000000000000 : ℝ)*base76 + (6776370626987/1562500000000000000000000000 : ℝ)*base78 + (1747687710653/390625000000000000000000000 : ℝ)*base80 + (4124325373013/781250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (2988653/1000000000000000000000 : ℝ)*base90 + (2988653/1000000000000000000000 : ℝ)*base92 + (2988653/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (103698810684703779874827/12500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (512428537/50000000000000 : ℝ)*(base19) + (29088657/2500000000000 : ℝ)*(base23) + (99141539/50000000000000 : ℝ)*(base32) + (227408059/100000000000000 : ℝ)*(upper3) + (6346259/6250000000000 : ℝ)*(upper5) + (284575572287977/25000000000000 : ℝ)*(major0) + (284575572287977/25000000000000 : ℝ)*(major1) + (284575572287977/25000000000000 : ℝ)*(major2) + (191011601/5000000000000 : ℝ)*(sp1) + (1144288207/20000000000000 : ℝ)*(sp2) + (88309801494793/5000000000000 : ℝ)*(sp4) + (1766191184806767/100000000000000 : ℝ)*(sp5) + (6899176347299/390625000000 : ℝ)*(sp6) + (51040807359471/10000000000000 : ℝ)*(sp7) + (127602067969447/25000000000000 : ℝ)*(f.failure) + (88309801494793/5000000000000 : ℝ)*(f.sum) + (19837383752797/12500000000000000000000000000 : ℝ)*base66 + (154550562627797/25000000000000000000000000000 : ℝ)*base68 + (2680929872203/25000000000000000000000000000 : ℝ)*base69 + (118642091252797/25000000000000000000000000000 : ℝ)*base72 + (50852522015297/12500000000000000000000000000 : ℝ)*base74 + (182304512827797/25000000000000000000000000000 : ℝ)*base76 + (154350857197203/25000000000000000000000000000 : ℝ)*base77 + (2571829247203/25000000000000000000000000000 : ℝ)*base79 + (27378519427797/12500000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base88 + (11614659/1250000000000000000000 : ℝ)*base89 + (11614659/1250000000000000000000 : ℝ)*base91 + (11614659/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1763_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5967/1024 : ℝ) ≤ p) (hpb : p ≤ (5983/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (111508997/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (3603/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (20143/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1763_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1763_s1_0 (p : ℝ) (hpa : (5967/1024 : ℝ) ≤ p) (hpb : p ≤ (5983/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-144100309/1250000000 : ℝ)*x 0 + (2740965201/5000000000 : ℝ)*x 1 + (1270733543/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (144100309/1250000000 : ℝ)^5983 ≤ (1475854757571/20000000000000 : ℝ)^4959 := by
    have hnat : (144100309 : ℕ)^5983*20000000000000^4959 ≤ 1475854757571^4959*1250000000^5983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      144100309 1250000000 1475854757571 20000000000000 5983 4959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2740965201/5000000000 : ℝ)^5983 ≤ (24210014903239/50000000000000 : ℝ)^4959 := by
    have hnat : (2740965201 : ℕ)^5983*50000000000000^4959 ≤ 24210014903239^4959*5000000000^5983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2740965201 5000000000 24210014903239 50000000000000 5983 4959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1270733543/2500000000 : ℝ)^5983 ≤ (44200696391603/100000000000000 : ℝ)^4959 := by
    have hnat : (1270733543 : ℕ)^5983*100000000000000^4959 ≤ 44200696391603^4959*2500000000^5983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1270733543 2500000000 44200696391603 100000000000000 5983 4959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5983/1024 : ℝ)) 5983 4959 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-144100309/1250000000 : ℝ), (2740965201/5000000000 : ℝ), (1270733543/2500000000 : ℝ)] ![(1475854757571/20000000000000 : ℝ), (24210014903239/50000000000000 : ℝ), (44200696391603/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-144100309/1250000000 : ℝ)|^5983 ≤ (1475854757571/20000000000000 : ℝ)^4959
        have hw : |(-144100309/1250000000 : ℝ)|=(144100309/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2740965201/5000000000 : ℝ)|^5983 ≤ (24210014903239/50000000000000 : ℝ)^4959
        have hw : |(2740965201/5000000000 : ℝ)|=(2740965201/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1270733543/2500000000 : ℝ)|^5983 ≤ (44200696391603/100000000000000 : ℝ)^4959
        have hw : |(1270733543/2500000000 : ℝ)|=(1270733543/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1763_s1_1 (p : ℝ) (hpa : (5967/1024 : ℝ) ≤ p) (hpb : p ≤ (5983/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2663899583/5000000000 : ℝ)*x 0 + (-680571273/5000000000 : ℝ)*x 1 + (5082934911/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2663899583/5000000000 : ℝ)^5983 ≤ (46782327285597/100000000000000 : ℝ)^4959 := by
    have hnat : (2663899583 : ℕ)^5983*100000000000000^4959 ≤ 46782327285597^4959*5000000000^5983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2663899583 5000000000 46782327285597 100000000000000 5983 4959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (680571273/5000000000 : ℝ)^5983 ≤ (9016968558077/100000000000000 : ℝ)^4959 := by
    have hnat : (680571273 : ℕ)^5983*100000000000000^4959 ≤ 9016968558077^4959*5000000000^5983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      680571273 5000000000 9016968558077 100000000000000 5983 4959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5082934911/10000000000 : ℝ)^5983 ≤ (5525088018107/12500000000000 : ℝ)^4959 := by
    have hnat : (5082934911 : ℕ)^5983*12500000000000^4959 ≤ 5525088018107^4959*10000000000^5983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5082934911 10000000000 5525088018107 12500000000000 5983 4959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5983/1024 : ℝ)) 5983 4959 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2663899583/5000000000 : ℝ), (-680571273/5000000000 : ℝ), (5082934911/10000000000 : ℝ)] ![(46782327285597/100000000000000 : ℝ), (9016968558077/100000000000000 : ℝ), (5525088018107/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2663899583/5000000000 : ℝ)|^5983 ≤ (46782327285597/100000000000000 : ℝ)^4959
        have hw : |(2663899583/5000000000 : ℝ)|=(2663899583/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-680571273/5000000000 : ℝ)|^5983 ≤ (9016968558077/100000000000000 : ℝ)^4959
        have hw : |(-680571273/5000000000 : ℝ)|=(680571273/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5082934911/10000000000 : ℝ)|^5983 ≤ (5525088018107/12500000000000 : ℝ)^4959
        have hw : |(5082934911/10000000000 : ℝ)|=(5082934911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1763_s1_2 (p : ℝ) (hpa : (5967/1024 : ℝ) ≤ p) (hpb : p ≤ (5983/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (532779979/1000000000 : ℝ)*x 0 + (203317367/400000000 : ℝ)*x 1 + (-680571343/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (532779979/1000000000 : ℝ)^5983 ≤ (11695583474059/25000000000000 : ℝ)^4959 := by
    have hnat : (532779979 : ℕ)^5983*25000000000000^4959 ≤ 11695583474059^4959*1000000000^5983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      532779979 1000000000 11695583474059 25000000000000 5983 4959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (203317367/400000000 : ℝ)^5983 ≤ (44200696423077/100000000000000 : ℝ)^4959 := by
    have hnat : (203317367 : ℕ)^5983*100000000000000^4959 ≤ 44200696423077^4959*400000000^5983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      203317367 400000000 44200696423077 100000000000000 5983 4959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (680571343/5000000000 : ℝ)^5983 ≤ (360678787081/4000000000000 : ℝ)^4959 := by
    have hnat : (680571343 : ℕ)^5983*4000000000000^4959 ≤ 360678787081^4959*5000000000^5983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      680571343 5000000000 360678787081 4000000000000 5983 4959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5983/1024 : ℝ)) 5983 4959 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(532779979/1000000000 : ℝ), (203317367/400000000 : ℝ), (-680571343/5000000000 : ℝ)] ![(11695583474059/25000000000000 : ℝ), (44200696423077/100000000000000 : ℝ), (360678787081/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(532779979/1000000000 : ℝ)|^5983 ≤ (11695583474059/25000000000000 : ℝ)^4959
        have hw : |(532779979/1000000000 : ℝ)|=(532779979/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(203317367/400000000 : ℝ)|^5983 ≤ (44200696423077/100000000000000 : ℝ)^4959
        have hw : |(203317367/400000000 : ℝ)|=(203317367/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-680571343/5000000000 : ℝ)|^5983 ≤ (360678787081/4000000000000 : ℝ)^4959
        have hw : |(-680571343/5000000000 : ℝ)|=(680571343/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1763_s1_3 (p : ℝ) (hpa : (5967/1024 : ℝ) ≤ p) (hpb : p ≤ (5983/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (499288853/1250000000 : ℝ)*x 0 + (3334573987/10000000000 : ℝ)*x 1 + (117881097/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (499288853/1250000000 : ℝ)^5983 ≤ (33047780172429/100000000000000 : ℝ)^4959 := by
    have hnat : (499288853 : ℕ)^5983*100000000000000^4959 ≤ 33047780172429^4959*1250000000^5983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      499288853 1250000000 33047780172429 100000000000000 5983 4959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3334573987/10000000000 : ℝ)^5983 ≤ (26579781952327/100000000000000 : ℝ)^4959 := by
    have hnat : (3334573987 : ℕ)^5983*100000000000000^4959 ≤ 26579781952327^4959*10000000000^5983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3334573987 10000000000 26579781952327 100000000000000 5983 4959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (117881097/250000000 : ℝ)^5983 ≤ (40372437857167/100000000000000 : ℝ)^4959 := by
    have hnat : (117881097 : ℕ)^5983*100000000000000^4959 ≤ 40372437857167^4959*250000000^5983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      117881097 250000000 40372437857167 100000000000000 5983 4959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5983/1024 : ℝ)) 5983 4959 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(499288853/1250000000 : ℝ), (3334573987/10000000000 : ℝ), (117881097/250000000 : ℝ)] ![(33047780172429/100000000000000 : ℝ), (26579781952327/100000000000000 : ℝ), (40372437857167/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(499288853/1250000000 : ℝ)|^5983 ≤ (33047780172429/100000000000000 : ℝ)^4959
        have hw : |(499288853/1250000000 : ℝ)|=(499288853/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3334573987/10000000000 : ℝ)|^5983 ≤ (26579781952327/100000000000000 : ℝ)^4959
        have hw : |(3334573987/10000000000 : ℝ)|=(3334573987/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(117881097/250000000 : ℝ)|^5983 ≤ (40372437857167/100000000000000 : ℝ)^4959
        have hw : |(117881097/250000000 : ℝ)|=(117881097/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1763_s1_4 (p : ℝ) (hpa : (5967/1024 : ℝ) ≤ p) (hpb : p ≤ (5983/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-288283959/2500000000 : ℝ)*x 0 + (508961613/1000000000 : ℝ)*x 1 + (1368777133/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (288283959/2500000000 : ℝ)^5983 ≤ (738184842057/10000000000000 : ℝ)^4959 := by
    have hnat : (288283959 : ℕ)^5983*10000000000000^4959 ≤ 738184842057^4959*2500000000^5983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      288283959 2500000000 738184842057 10000000000000 5983 4959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (508961613/1000000000 : ℝ)^5983 ≤ (44270809978171/100000000000000 : ℝ)^4959 := by
    have hnat : (508961613 : ℕ)^5983*100000000000000^4959 ≤ 44270809978171^4959*1000000000^5983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      508961613 1000000000 44270809978171 100000000000000 5983 4959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1368777133/2500000000 : ℝ)^5983 ≤ (48347341584261/100000000000000 : ℝ)^4959 := by
    have hnat : (1368777133 : ℕ)^5983*100000000000000^4959 ≤ 48347341584261^4959*2500000000^5983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1368777133 2500000000 48347341584261 100000000000000 5983 4959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5983/1024 : ℝ)) 5983 4959 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-288283959/2500000000 : ℝ), (508961613/1000000000 : ℝ), (1368777133/2500000000 : ℝ)] ![(738184842057/10000000000000 : ℝ), (44270809978171/100000000000000 : ℝ), (48347341584261/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-288283959/2500000000 : ℝ)|^5983 ≤ (738184842057/10000000000000 : ℝ)^4959
        have hw : |(-288283959/2500000000 : ℝ)|=(288283959/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(508961613/1000000000 : ℝ)|^5983 ≤ (44270809978171/100000000000000 : ℝ)^4959
        have hw : |(508961613/1000000000 : ℝ)|=(508961613/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1368777133/2500000000 : ℝ)|^5983 ≤ (48347341584261/100000000000000 : ℝ)^4959
        have hw : |(1368777133/2500000000 : ℝ)|=(1368777133/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1763_s1_5 (p : ℝ) (hpa : (5967/1024 : ℝ) ≤ p) (hpb : p ≤ (5983/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1305615699/2500000000 : ℝ)*x 0 + (-193793763/2000000000 : ℝ)*x 1 + (1368777107/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1305615699/2500000000 : ℝ)^5983 ≤ (45668686565831/100000000000000 : ℝ)^4959 := by
    have hnat : (1305615699 : ℕ)^5983*100000000000000^4959 ≤ 45668686565831^4959*2500000000^5983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1305615699 2500000000 45668686565831 100000000000000 5983 4959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (193793763/2000000000 : ℝ)^5983 ≤ (2991986474949/50000000000000 : ℝ)^4959 := by
    have hnat : (193793763 : ℕ)^5983*50000000000000^4959 ≤ 2991986474949^4959*2000000000^5983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      193793763 2000000000 2991986474949 50000000000000 5983 4959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1368777107/2500000000 : ℝ)^5983 ≤ (9669468095253/20000000000000 : ℝ)^4959 := by
    have hnat : (1368777107 : ℕ)^5983*20000000000000^4959 ≤ 9669468095253^4959*2500000000^5983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1368777107 2500000000 9669468095253 20000000000000 5983 4959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5983/1024 : ℝ)) 5983 4959 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1305615699/2500000000 : ℝ), (-193793763/2000000000 : ℝ), (1368777107/2500000000 : ℝ)] ![(45668686565831/100000000000000 : ℝ), (2991986474949/50000000000000 : ℝ), (9669468095253/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1305615699/2500000000 : ℝ)|^5983 ≤ (45668686565831/100000000000000 : ℝ)^4959
        have hw : |(1305615699/2500000000 : ℝ)|=(1305615699/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-193793763/2000000000 : ℝ)|^5983 ≤ (2991986474949/50000000000000 : ℝ)^4959
        have hw : |(-193793763/2000000000 : ℝ)|=(193793763/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1368777107/2500000000 : ℝ)|^5983 ≤ (9669468095253/20000000000000 : ℝ)^4959
        have hw : |(1368777107/2500000000 : ℝ)|=(1368777107/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1763_s1_6 (p : ℝ) (hpa : (5967/1024 : ℝ) ≤ p) (hpb : p ≤ (5983/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5222463019/10000000000 : ℝ)*x 0 + (2737554143/5000000000 : ℝ)*x 1 + (-968968701/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5222463019/10000000000 : ℝ)^5983 ≤ (9133737783713/20000000000000 : ℝ)^4959 := by
    have hnat : (5222463019 : ℕ)^5983*20000000000000^4959 ≤ 9133737783713^4959*10000000000^5983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5222463019 10000000000 9133737783713 20000000000000 5983 4959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2737554143/5000000000 : ℝ)^5983 ≤ (1933893558537/4000000000000 : ℝ)^4959 := by
    have hnat : (2737554143 : ℕ)^5983*4000000000000^4959 ≤ 1933893558537^4959*5000000000^5983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2737554143 5000000000 1933893558537 4000000000000 5983 4959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (968968701/10000000000 : ℝ)^5983 ≤ (747996512563/12500000000000 : ℝ)^4959 := by
    have hnat : (968968701 : ℕ)^5983*12500000000000^4959 ≤ 747996512563^4959*10000000000^5983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      968968701 10000000000 747996512563 12500000000000 5983 4959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5983/1024 : ℝ)) 5983 4959 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5222463019/10000000000 : ℝ), (2737554143/5000000000 : ℝ), (-968968701/10000000000 : ℝ)] ![(9133737783713/20000000000000 : ℝ), (1933893558537/4000000000000 : ℝ), (747996512563/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5222463019/10000000000 : ℝ)|^5983 ≤ (9133737783713/20000000000000 : ℝ)^4959
        have hw : |(5222463019/10000000000 : ℝ)|=(5222463019/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2737554143/5000000000 : ℝ)|^5983 ≤ (1933893558537/4000000000000 : ℝ)^4959
        have hw : |(2737554143/5000000000 : ℝ)|=(2737554143/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-968968701/10000000000 : ℝ)|^5983 ≤ (747996512563/12500000000000 : ℝ)^4959
        have hw : |(-968968701/10000000000 : ℝ)|=(968968701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1763_s1_7 (p : ℝ) (hpa : (5967/1024 : ℝ) ≤ p) (hpb : p ≤ (5983/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1278549/3200000 : ℝ)*x 0 + (4692123377/10000000000 : ℝ)*x 1 + (3358180643/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1278549/3200000 : ℝ)^5983 ≤ (16529653973089/50000000000000 : ℝ)^4959 := by
    have hnat : (1278549 : ℕ)^5983*50000000000000^4959 ≤ 16529653973089^4959*3200000^5983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1278549 3200000 16529653973089 50000000000000 5983 4959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4692123377/10000000000 : ℝ)^5983 ≤ (40133721168139/100000000000000 : ℝ)^4959 := by
    have hnat : (4692123377 : ℕ)^5983*100000000000000^4959 ≤ 40133721168139^4959*10000000000^5983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4692123377 10000000000 40133721168139 100000000000000 5983 4959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3358180643/10000000000 : ℝ)^5983 ≤ (13403485436563/50000000000000 : ℝ)^4959 := by
    have hnat : (3358180643 : ℕ)^5983*50000000000000^4959 ≤ 13403485436563^4959*10000000000^5983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3358180643 10000000000 13403485436563 50000000000000 5983 4959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5983/1024 : ℝ)) 5983 4959 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1278549/3200000 : ℝ), (4692123377/10000000000 : ℝ), (3358180643/10000000000 : ℝ)] ![(16529653973089/50000000000000 : ℝ), (40133721168139/100000000000000 : ℝ), (13403485436563/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1278549/3200000 : ℝ)|^5983 ≤ (16529653973089/50000000000000 : ℝ)^4959
        have hw : |(1278549/3200000 : ℝ)|=(1278549/3200000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4692123377/10000000000 : ℝ)|^5983 ≤ (40133721168139/100000000000000 : ℝ)^4959
        have hw : |(4692123377/10000000000 : ℝ)|=(4692123377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3358180643/10000000000 : ℝ)|^5983 ≤ (13403485436563/50000000000000 : ℝ)^4959
        have hw : |(3358180643/10000000000 : ℝ)|=(3358180643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1763_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5967/1024 : ℝ) ≤ p) (hpb : p ≤ (5983/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (111508997/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (20143/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3603/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (9153/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3553/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (20143/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (3603/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (20143/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (3603/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (20143/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (3603/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (20143/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (3603/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (20143/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (3603/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (20143/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (3603/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (3603/50000 : ℝ) ^ (5967/1024 : ℝ) ≤ (4412095201163/20000000000000000000 : ℝ) := by
    have hpowers : (3603/50000 : ℝ)^5967 ≤ (4412095201163/20000000000000000000 : ℝ)^1024 := by
      have hnat : (3603 : ℕ)^5967*20000000000000000000^1024 ≤ 4412095201163^1024*50000^5967 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3603 50000 4412095201163 20000000000000000000 5967 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3603/50000 : ℝ)) (X := (4412095201163/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5967 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (20143/100000 : ℝ) ^ (5967/1024 : ℝ) ≤ (4405529850569209/50000000000000000000 : ℝ) := by
    have hpowers : (20143/100000 : ℝ)^5967 ≤ (4405529850569209/50000000000000000000 : ℝ)^1024 := by
      have hnat : (20143 : ℕ)^5967*50000000000000000000^1024 ≤ 4405529850569209^1024*100000^5967 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20143 100000 4405529850569209 50000000000000000000 5967 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (20143/100000 : ℝ)) (X := (4405529850569209/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5967 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000004412095201163/10000000000000000000 : ℝ) ≤ (5000000378580917/5000000000000000 : ℝ) ^ (5967/1024 : ℝ) := by
    have hpowers : (10000004412095201163/10000000000000000000 : ℝ)^1024 ≤ (5000000378580917/5000000000000000 : ℝ)^5967 := by
      have hnat : (10000004412095201163 : ℕ)^1024*5000000000000000^5967 ≤ 5000000378580917^5967*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000004412095201163 10000000000000000000 5000000378580917 5000000000000000 1024 5967 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000378580917/5000000000000000 : ℝ)) (X := (10000004412095201163/10000000000000000000 : ℝ)) (by norm_num) 5967 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100008833120177144233/100000000000000000000 : ℝ) ≤ (10000151580093041/10000000000000000 : ℝ) ^ (5967/1024 : ℝ) := by
    have hpowers : (100008833120177144233/100000000000000000000 : ℝ)^1024 ≤ (10000151580093041/10000000000000000 : ℝ)^5967 := by
      have hnat : (100008833120177144233 : ℕ)^1024*10000000000000000^5967 ≤ 10000151580093041^5967*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100008833120177144233 100000000000000000000 10000151580093041 10000000000000000 1024 5967 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000151580093041/10000000000000000 : ℝ)) (X := (100008833120177144233/100000000000000000000 : ℝ)) (by norm_num) 5967 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25004405529850569209/25000000000000000000 : ℝ) ≤ (1250037800378031/1250000000000000 : ℝ) ^ (5967/1024 : ℝ) := by
    have hpowers : (25004405529850569209/25000000000000000000 : ℝ)^1024 ≤ (1250037800378031/1250000000000000 : ℝ)^5967 := by
      have hnat : (25004405529850569209 : ℕ)^1024*1250000000000000^5967 ≤ 1250037800378031^5967*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25004405529850569209 25000000000000000000 1250037800378031 1250000000000000 1024 5967 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250037800378031/1250000000000000 : ℝ)) (X := (25004405529850569209/25000000000000000000 : ℝ)) (by norm_num) 5967 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4412095201163/20000000000000000000 : ℝ) ≤ ((64683918067659045587/64685000000000000000 : ℝ)+2*(150822931207/1293700000000000 : ℝ)*(3603/50000 : ℝ))^(5967/1024 : ℝ) := by
    rw [show (64683918067659045587/64685000000000000000 : ℝ)+2*(150822931207/1293700000000000 : ℝ)*(3603/50000 : ℝ)=(5000000378580917/5000000000000000 : ℝ) by norm_num, show 1+2*(4412095201163/20000000000000000000 : ℝ)=(10000004412095201163/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(4405529850569209/50000000000000000000 : ℝ)+(4412095201163/20000000000000000000 : ℝ) ≤ ((64683918067659045587/64685000000000000000 : ℝ)+(150822931207/1293700000000000 : ℝ)*((20143/100000 : ℝ)+(3603/50000 : ℝ)))^(5967/1024 : ℝ) := by
    rw [show (64683918067659045587/64685000000000000000 : ℝ)+(150822931207/1293700000000000 : ℝ)*((20143/100000 : ℝ)+(3603/50000 : ℝ))=(10000151580093041/10000000000000000 : ℝ) by norm_num, show 1+(4405529850569209/50000000000000000000 : ℝ)+(4412095201163/20000000000000000000 : ℝ)=(100008833120177144233/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(4405529850569209/50000000000000000000 : ℝ) ≤ ((64683918067659045587/64685000000000000000 : ℝ)+2*(150822931207/1293700000000000 : ℝ)*(20143/100000 : ℝ))^(5967/1024 : ℝ) := by
    rw [show (64683918067659045587/64685000000000000000 : ℝ)+2*(150822931207/1293700000000000 : ℝ)*(20143/100000 : ℝ)=(1250037800378031/1250000000000000 : ℝ) by norm_num, show 1+2*(4405529850569209/50000000000000000000 : ℝ)=(25004405529850569209/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (64683918067659045587/64685000000000000000 : ℝ)*(X 1 0+X 2 0)+(150822931207/1293700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5967/1024 : ℝ)) (lo := (3603/50000 : ℝ)) (hi := (20143/100000 : ℝ)) (c := (64683918067659045587/64685000000000000000 : ℝ)) (alpha := (150822931207/1293700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (64683918067659045587/64685000000000000000 : ℝ)*(X 0 1+X 2 1)+(150822931207/1293700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5967/1024 : ℝ)) (lo := (3603/50000 : ℝ)) (hi := (20143/100000 : ℝ)) (c := (64683918067659045587/64685000000000000000 : ℝ)) (alpha := (150822931207/1293700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (64683918067659045587/64685000000000000000 : ℝ)*(X 0 2+X 1 2)+(150822931207/1293700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5967/1024 : ℝ)) (lo := (3603/50000 : ℝ)) (hi := (20143/100000 : ℝ)) (c := (64683918067659045587/64685000000000000000 : ℝ)) (alpha := (150822931207/1293700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-144100309/1250000000 : ℝ)*X 0 0+(2740965201/5000000000 : ℝ)*X 0 1+(1270733543/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1763_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2663899583/5000000000 : ℝ)*X 1 0+(-680571273/5000000000 : ℝ)*X 1 1+(5082934911/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1763_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((532779979/1000000000 : ℝ)*X 2 0+(203317367/400000000 : ℝ)*X 2 1+(-680571343/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1763_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((499288853/1250000000 : ℝ)*X 0 0+(3334573987/10000000000 : ℝ)*X 0 1+(117881097/250000000 : ℝ)*X 0 2+(499288853/1250000000 : ℝ)*X 1 0+(3334573987/10000000000 : ℝ)*X 1 1+(117881097/250000000 : ℝ)*X 1 2+(499288853/1250000000 : ℝ)*X 2 0+(3334573987/10000000000 : ℝ)*X 2 1+(117881097/250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1763_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-288283959/2500000000 : ℝ)*X 0 0+(508961613/1000000000 : ℝ)*X 0 1+(1368777133/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1763_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1305615699/2500000000 : ℝ)*X 1 0+(-193793763/2000000000 : ℝ)*X 1 1+(1368777107/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1763_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5222463019/10000000000 : ℝ)*X 2 0+(2737554143/5000000000 : ℝ)*X 2 1+(-968968701/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1763_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1278549/3200000 : ℝ)*X 0 0+(4692123377/10000000000 : ℝ)*X 0 1+(3358180643/10000000000 : ℝ)*X 0 2+(1278549/3200000 : ℝ)*X 1 0+(4692123377/10000000000 : ℝ)*X 1 1+(3358180643/10000000000 : ℝ)*X 1 2+(1278549/3200000 : ℝ)*X 2 0+(4692123377/10000000000 : ℝ)*X 2 1+(3358180643/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1763_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (39207917656726676945683901577/3234250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (441284331/25000000000000 : ℝ)*(base19) + (410665439/20000000000000 : ℝ)*(base23) + (713187/25000000000000 : ℝ)*(lower2) + (353820363/100000000000000 : ℝ)*(upper3) + (152856751/50000000000000 : ℝ)*(upper5) + (1615310489821419/100000000000000 : ℝ)*(major0) + (1615310489821419/100000000000000 : ℝ)*(major1) + (1615310489821419/100000000000000 : ℝ)*(major2) + (626576676912489/25000000000000 : ℝ)*(sp0) + (626580693635889/25000000000000 : ℝ)*(sp1) + (1253161243176843/50000000000000 : ℝ)*(sp2) + (724290785472873/100000000000000 : ℝ)*(sp3) + (713281237/4000000000000 : ℝ)*(sp4) + (164074947/3125000000000 : ℝ)*(sp7) + (724296035871177/100000000000000 : ℝ)*(f.failure) + (31329056746011/1250000000000 : ℝ)*(f.sum) + (105859111536033/64685000000000000000000000000 : ℝ)*base65 + (2601199963391822047/6468500000000000000000000000000000 : ℝ)*base68 + (56994528117067322047/6468500000000000000000000000000000 : ℝ)*base70 + (25716137791341322047/6468500000000000000000000000000000 : ℝ)*base72 + (57767480718939/32342500000000000000000000000 : ℝ)*base73 + (39920501811071322047/6468500000000000000000000000000000 : ℝ)*base76 + (41557828350555322047/6468500000000000000000000000000000 : ℝ)*base78 + (37514517886019822047/6468500000000000000000000000000000 : ℝ)*base80 + (181128717740727/64685000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (18479469/5000000000000000000000 : ℝ)*base89 + (18479469/5000000000000000000000 : ℝ)*base91 + (18479469/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (22955208539688275741955544833/1617125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (853632289/50000000000000 : ℝ)*(base19) + (413329961/20000000000000 : ℝ)*(base23) + (58517369/20000000000000 : ℝ)*(upper3) + (25591249/25000000000000 : ℝ)*(lower4) + (265319791/100000000000000 : ℝ)*(upper5) + (1671870647968447/100000000000000 : ℝ)*(major0) + (1671870647968447/100000000000000 : ℝ)*(major1) + (1671870647968447/100000000000000 : ℝ)*(major2) + (11549821107/100000000000000 : ℝ)*(sp1) + (14158038669/100000000000000 : ℝ)*(sp2) + (648520883423347/25000000000000 : ℝ)*(sp4) + (1297035138303851/50000000000000 : ℝ)*(sp5) + (1297033654502457/50000000000000 : ℝ)*(sp6) + (187414322268593/25000000000000 : ℝ)*(sp7) + (187414322268593/25000000000000 : ℝ)*(f.failure) + (648520883423347/25000000000000 : ℝ)*(f.sum) + (21995016762891/64685000000000000000000000000 : ℝ)*base66 + (11750558264333043389/6468500000000000000000000000000000 : ℝ)*base67 + (18565608617565043389/6468500000000000000000000000000000 : ℝ)*base69 + (51907838307488043389/6468500000000000000000000000000000 : ℝ)*base71 + (63655556606491/64685000000000000000000000000 : ℝ)*base74 + (64271431171350543389/6468500000000000000000000000000000 : ℝ)*base75 + (36005009569131043389/6468500000000000000000000000000000 : ℝ)*base77 + (5381794654938456611/6468500000000000000000000000000000 : ℝ)*base80 + (861465763149/64685000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (17468779/1250000000000000000000 : ℝ)*base90 + (17468779/1250000000000000000000 : ℝ)*base92 + (17468779/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1763_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5967/1024 : ℝ) ≤ p) (hpb : p ≤ (5983/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (111508997/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (20143/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3603/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9153/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3553/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1763_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1763_s2_0 (p : ℝ) (hpa : (5967/1024 : ℝ) ≤ p) (hpb : p ≤ (5983/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-576688049/5000000000 : ℝ)*x 0 + (5480081343/10000000000 : ℝ)*x 1 + (5084389927/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (576688049/5000000000 : ℝ)^5983 ≤ (7383704104379/100000000000000 : ℝ)^4959 := by
    have hnat : (576688049 : ℕ)^5983*100000000000000^4959 ≤ 7383704104379^4959*5000000000^5983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      576688049 5000000000 7383704104379 100000000000000 5983 4959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5480081343/10000000000 : ℝ)^5983 ≤ (24200162956013/50000000000000 : ℝ)^4959 := by
    have hnat : (5480081343 : ℕ)^5983*50000000000000^4959 ≤ 24200162956013^4959*10000000000^5983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5480081343 10000000000 24200162956013 50000000000000 5983 4959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5084389927/10000000000 : ℝ)^5983 ≤ (690874530701/1562500000000 : ℝ)^4959 := by
    have hnat : (5084389927 : ℕ)^5983*1562500000000^4959 ≤ 690874530701^4959*10000000000^5983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5084389927 10000000000 690874530701 1562500000000 5983 4959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5983/1024 : ℝ)) 5983 4959 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-576688049/5000000000 : ℝ), (5480081343/10000000000 : ℝ), (5084389927/10000000000 : ℝ)] ![(7383704104379/100000000000000 : ℝ), (24200162956013/50000000000000 : ℝ), (690874530701/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-576688049/5000000000 : ℝ)|^5983 ≤ (7383704104379/100000000000000 : ℝ)^4959
        have hw : |(-576688049/5000000000 : ℝ)|=(576688049/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5480081343/10000000000 : ℝ)|^5983 ≤ (24200162956013/50000000000000 : ℝ)^4959
        have hw : |(5480081343/10000000000 : ℝ)|=(5480081343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5084389927/10000000000 : ℝ)|^5983 ≤ (690874530701/1562500000000 : ℝ)^4959
        have hw : |(5084389927/10000000000 : ℝ)|=(5084389927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1763_s2_1 (p : ℝ) (hpa : (5967/1024 : ℝ) ≤ p) (hpb : p ≤ (5983/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2663640867/5000000000 : ℝ)*x 0 + (-67995909/500000000 : ℝ)*x 1 + (158887187/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2663640867/5000000000 : ℝ)^5983 ≤ (46776845679799/100000000000000 : ℝ)^4959 := by
    have hnat : (2663640867 : ℕ)^5983*100000000000000^4959 ≤ 46776845679799^4959*5000000000^5983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2663640867 5000000000 46776845679799 100000000000000 5983 4959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (67995909/500000000 : ℝ)^5983 ≤ (4503591869989/50000000000000 : ℝ)^4959 := by
    have hnat : (67995909 : ℕ)^5983*50000000000000^4959 ≤ 4503591869989^4959*500000000^5983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67995909 500000000 4503591869989 50000000000000 5983 4959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (158887187/312500000 : ℝ)^5983 ≤ (44215970562917/100000000000000 : ℝ)^4959 := by
    have hnat : (158887187 : ℕ)^5983*100000000000000^4959 ≤ 44215970562917^4959*312500000^5983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      158887187 312500000 44215970562917 100000000000000 5983 4959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5983/1024 : ℝ)) 5983 4959 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2663640867/5000000000 : ℝ), (-67995909/500000000 : ℝ), (158887187/312500000 : ℝ)] ![(46776845679799/100000000000000 : ℝ), (4503591869989/50000000000000 : ℝ), (44215970562917/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2663640867/5000000000 : ℝ)|^5983 ≤ (46776845679799/100000000000000 : ℝ)^4959
        have hw : |(2663640867/5000000000 : ℝ)|=(2663640867/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-67995909/500000000 : ℝ)|^5983 ≤ (4503591869989/50000000000000 : ℝ)^4959
        have hw : |(-67995909/500000000 : ℝ)|=(67995909/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(158887187/312500000 : ℝ)|^5983 ≤ (44215970562917/100000000000000 : ℝ)^4959
        have hw : |(158887187/312500000 : ℝ)|=(158887187/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1763_s2_2 (p : ℝ) (hpa : (5967/1024 : ℝ) ≤ p) (hpb : p ≤ (5983/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5327281921/10000000000 : ℝ)*x 0 + (1271097463/2500000000 : ℝ)*x 1 + (-1359918107/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5327281921/10000000000 : ℝ)^5983 ≤ (1461776489401/3125000000000 : ℝ)^4959 := by
    have hnat : (5327281921 : ℕ)^5983*3125000000000^4959 ≤ 1461776489401^4959*10000000000^5983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5327281921 10000000000 1461776489401 3125000000000 5983 4959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1271097463/2500000000 : ℝ)^5983 ≤ (44215969177951/100000000000000 : ℝ)^4959 := by
    have hnat : (1271097463 : ℕ)^5983*100000000000000^4959 ≤ 44215969177951^4959*2500000000^5983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1271097463 2500000000 44215969177951 100000000000000 5983 4959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1359918107/10000000000 : ℝ)^5983 ≤ (1801436631327/20000000000000 : ℝ)^4959 := by
    have hnat : (1359918107 : ℕ)^5983*20000000000000^4959 ≤ 1801436631327^4959*10000000000^5983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1359918107 10000000000 1801436631327 20000000000000 5983 4959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5983/1024 : ℝ)) 5983 4959 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5327281921/10000000000 : ℝ), (1271097463/2500000000 : ℝ), (-1359918107/10000000000 : ℝ)] ![(1461776489401/3125000000000 : ℝ), (44215969177951/100000000000000 : ℝ), (1801436631327/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5327281921/10000000000 : ℝ)|^5983 ≤ (1461776489401/3125000000000 : ℝ)^4959
        have hw : |(5327281921/10000000000 : ℝ)|=(5327281921/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1271097463/2500000000 : ℝ)|^5983 ≤ (44215969177951/100000000000000 : ℝ)^4959
        have hw : |(1271097463/2500000000 : ℝ)|=(1271097463/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1359918107/10000000000 : ℝ)|^5983 ≤ (1801436631327/20000000000000 : ℝ)^4959
        have hw : |(-1359918107/10000000000 : ℝ)|=(1359918107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1763_s2_3 (p : ℝ) (hpa : (5967/1024 : ℝ) ≤ p) (hpb : p ≤ (5983/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (399478349/1000000000 : ℝ)*x 0 + (3340258619/10000000000 : ℝ)*x 1 + (4709493319/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (399478349/1000000000 : ℝ)^5983 ≤ (8263124616611/25000000000000 : ℝ)^4959 := by
    have hnat : (399478349 : ℕ)^5983*25000000000000^4959 ≤ 8263124616611^4959*1000000000^5983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      399478349 1000000000 8263124616611 25000000000000 5983 4959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3340258619/10000000000 : ℝ)^5983 ≤ (13317230107379/50000000000000 : ℝ)^4959 := by
    have hnat : (3340258619 : ℕ)^5983*50000000000000^4959 ≤ 13317230107379^4959*10000000000^5983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3340258619 10000000000 13317230107379 50000000000000 5983 4959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4709493319/10000000000 : ℝ)^5983 ≤ (40313041307447/100000000000000 : ℝ)^4959 := by
    have hnat : (4709493319 : ℕ)^5983*100000000000000^4959 ≤ 40313041307447^4959*10000000000^5983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4709493319 10000000000 40313041307447 100000000000000 5983 4959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5983/1024 : ℝ)) 5983 4959 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(399478349/1000000000 : ℝ), (3340258619/10000000000 : ℝ), (4709493319/10000000000 : ℝ)] ![(8263124616611/25000000000000 : ℝ), (13317230107379/50000000000000 : ℝ), (40313041307447/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(399478349/1000000000 : ℝ)|^5983 ≤ (8263124616611/25000000000000 : ℝ)^4959
        have hw : |(399478349/1000000000 : ℝ)|=(399478349/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3340258619/10000000000 : ℝ)|^5983 ≤ (13317230107379/50000000000000 : ℝ)^4959
        have hw : |(3340258619/10000000000 : ℝ)|=(3340258619/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4709493319/10000000000 : ℝ)|^5983 ≤ (40313041307447/100000000000000 : ℝ)^4959
        have hw : |(4709493319/10000000000 : ℝ)|=(4709493319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1763_s2_4 (p : ℝ) (hpa : (5967/1024 : ℝ) ≤ p) (hpb : p ≤ (5983/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-576850849/5000000000 : ℝ)*x 0 + (1018192273/2000000000 : ℝ)*x 1 + (2736686547/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (576850849/5000000000 : ℝ)^5983 ≤ (738621903081/10000000000000 : ℝ)^4959 := by
    have hnat : (576850849 : ℕ)^5983*10000000000000^4959 ≤ 738621903081^4959*5000000000^5983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      576850849 5000000000 738621903081 10000000000000 5983 4959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1018192273/2000000000 : ℝ)^5983 ≤ (22142463894251/50000000000000 : ℝ)^4959 := by
    have hnat : (1018192273 : ℕ)^5983*50000000000000^4959 ≤ 22142463894251^4959*2000000000^5983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1018192273 2000000000 22142463894251 50000000000000 5983 4959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2736686547/5000000000 : ℝ)^5983 ≤ (1510276661581/3125000000000 : ℝ)^4959 := by
    have hnat : (2736686547 : ℕ)^5983*3125000000000^4959 ≤ 1510276661581^4959*5000000000^5983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2736686547 5000000000 1510276661581 3125000000000 5983 4959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5983/1024 : ℝ)) 5983 4959 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-576850849/5000000000 : ℝ), (1018192273/2000000000 : ℝ), (2736686547/5000000000 : ℝ)] ![(738621903081/10000000000000 : ℝ), (22142463894251/50000000000000 : ℝ), (1510276661581/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-576850849/5000000000 : ℝ)|^5983 ≤ (738621903081/10000000000000 : ℝ)^4959
        have hw : |(-576850849/5000000000 : ℝ)|=(576850849/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1018192273/2000000000 : ℝ)|^5983 ≤ (22142463894251/50000000000000 : ℝ)^4959
        have hw : |(1018192273/2000000000 : ℝ)|=(1018192273/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2736686547/5000000000 : ℝ)|^5983 ≤ (1510276661581/3125000000000 : ℝ)^4959
        have hw : |(2736686547/5000000000 : ℝ)|=(2736686547/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1763_s2_5 (p : ℝ) (hpa : (5967/1024 : ℝ) ≤ p) (hpb : p ≤ (5983/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4080333/7812500 : ℝ)*x 0 + (-15170859/156250000 : ℝ)*x 1 + (5473373113/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4080333/7812500 : ℝ)^5983 ≤ (2854532566583/6250000000000 : ℝ)^4959 := by
    have hnat : (4080333 : ℕ)^5983*6250000000000^4959 ≤ 2854532566583^4959*7812500^5983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4080333 7812500 2854532566583 6250000000000 5983 4959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (15170859/156250000 : ℝ)^5983 ≤ (5998625550779/100000000000000 : ℝ)^4959 := by
    have hnat : (15170859 : ℕ)^5983*100000000000000^4959 ≤ 5998625550779^4959*156250000^5983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      15170859 156250000 5998625550779 100000000000000 5983 4959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5473373113/10000000000 : ℝ)^5983 ≤ (48328853373001/100000000000000 : ℝ)^4959 := by
    have hnat : (5473373113 : ℕ)^5983*100000000000000^4959 ≤ 48328853373001^4959*10000000000^5983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5473373113 10000000000 48328853373001 100000000000000 5983 4959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5983/1024 : ℝ)) 5983 4959 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4080333/7812500 : ℝ), (-15170859/156250000 : ℝ), (5473373113/10000000000 : ℝ)] ![(2854532566583/6250000000000 : ℝ), (5998625550779/100000000000000 : ℝ), (48328853373001/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4080333/7812500 : ℝ)|^5983 ≤ (2854532566583/6250000000000 : ℝ)^4959
        have hw : |(4080333/7812500 : ℝ)|=(4080333/7812500 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-15170859/156250000 : ℝ)|^5983 ≤ (5998625550779/100000000000000 : ℝ)^4959
        have hw : |(-15170859/156250000 : ℝ)|=(15170859/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5473373113/10000000000 : ℝ)|^5983 ≤ (48328853373001/100000000000000 : ℝ)^4959
        have hw : |(5473373113/10000000000 : ℝ)|=(5473373113/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1763_s2_6 (p : ℝ) (hpa : (5967/1024 : ℝ) ≤ p) (hpb : p ≤ (5983/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1305706567/2500000000 : ℝ)*x 0 + (5473373087/10000000000 : ℝ)*x 1 + (-970934973/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1305706567/2500000000 : ℝ)^5983 ≤ (45672521360743/100000000000000 : ℝ)^4959 := by
    have hnat : (1305706567 : ℕ)^5983*100000000000000^4959 ≤ 45672521360743^4959*2500000000^5983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1305706567 2500000000 45672521360743 100000000000000 5983 4959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5473373087/10000000000 : ℝ)^5983 ≤ (48328853096021/100000000000000 : ℝ)^4959 := by
    have hnat : (5473373087 : ℕ)^5983*100000000000000^4959 ≤ 48328853096021^4959*10000000000^5983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5473373087 10000000000 48328853096021 100000000000000 5983 4959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (970934973/10000000000 : ℝ)^5983 ≤ (2999312764209/50000000000000 : ℝ)^4959 := by
    have hnat : (970934973 : ℕ)^5983*50000000000000^4959 ≤ 2999312764209^4959*10000000000^5983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      970934973 10000000000 2999312764209 50000000000000 5983 4959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5983/1024 : ℝ)) 5983 4959 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1305706567/2500000000 : ℝ), (5473373087/10000000000 : ℝ), (-970934973/10000000000 : ℝ)] ![(45672521360743/100000000000000 : ℝ), (48328853096021/100000000000000 : ℝ), (2999312764209/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1305706567/2500000000 : ℝ)|^5983 ≤ (45672521360743/100000000000000 : ℝ)^4959
        have hw : |(1305706567/2500000000 : ℝ)|=(1305706567/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5473373087/10000000000 : ℝ)|^5983 ≤ (48328853096021/100000000000000 : ℝ)^4959
        have hw : |(5473373087/10000000000 : ℝ)|=(5473373087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-970934973/10000000000 : ℝ)|^5983 ≤ (2999312764209/50000000000000 : ℝ)^4959
        have hw : |(-970934973/10000000000 : ℝ)|=(970934973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1763_s2_7 (p : ℝ) (hpa : (5967/1024 : ℝ) ≤ p) (hpb : p ≤ (5983/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (39959103/100000000 : ℝ)*x 0 + (4686753903/10000000000 : ℝ)*x 1 + (420433953/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (39959103/100000000 : ℝ)^5983 ≤ (8265936771841/25000000000000 : ℝ)^4959 := by
    have hnat : (39959103 : ℕ)^5983*25000000000000^4959 ≤ 8265936771841^4959*100000000^5983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      39959103 100000000 8265936771841 25000000000000 5983 4959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4686753903/10000000000 : ℝ)^5983 ≤ (40078316633269/100000000000000 : ℝ)^4959 := by
    have hnat : (4686753903 : ℕ)^5983*100000000000000^4959 ≤ 40078316633269^4959*10000000000^5983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4686753903 10000000000 40078316633269 100000000000000 5983 4959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (420433953/1250000000 : ℝ)^5983 ≤ (26857936268377/100000000000000 : ℝ)^4959 := by
    have hnat : (420433953 : ℕ)^5983*100000000000000^4959 ≤ 26857936268377^4959*1250000000^5983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      420433953 1250000000 26857936268377 100000000000000 5983 4959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5983/1024 : ℝ)) 5983 4959 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(39959103/100000000 : ℝ), (4686753903/10000000000 : ℝ), (420433953/1250000000 : ℝ)] ![(8265936771841/25000000000000 : ℝ), (40078316633269/100000000000000 : ℝ), (26857936268377/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(39959103/100000000 : ℝ)|^5983 ≤ (8265936771841/25000000000000 : ℝ)^4959
        have hw : |(39959103/100000000 : ℝ)|=(39959103/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4686753903/10000000000 : ℝ)|^5983 ≤ (40078316633269/100000000000000 : ℝ)^4959
        have hw : |(4686753903/10000000000 : ℝ)|=(4686753903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(420433953/1250000000 : ℝ)|^5983 ≤ (26857936268377/100000000000000 : ℝ)^4959
        have hw : |(420433953/1250000000 : ℝ)|=(420433953/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1763_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5967/1024 : ℝ) ≤ p) (hpb : p ≤ (5983/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (111508997/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3553/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9153/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (4593/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (709/4000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3553/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9153/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3553/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9153/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3553/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9153/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3553/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9153/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3553/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9153/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3553/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9153/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9153/100000 : ℝ) ^ (5967/1024 : ℝ) ≤ (88894758056359/100000000000000000000 : ℝ) := by
    have hpowers : (9153/100000 : ℝ)^5967 ≤ (88894758056359/100000000000000000000 : ℝ)^1024 := by
      have hnat : (9153 : ℕ)^5967*100000000000000000000^1024 ≤ 88894758056359^1024*100000^5967 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9153 100000 88894758056359 100000000000000000000 5967 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9153/100000 : ℝ)) (X := (88894758056359/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5967 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3553/20000 : ℝ) ^ (5967/1024 : ℝ) ≤ (4237454974949373/100000000000000000000 : ℝ) := by
    have hpowers : (3553/20000 : ℝ)^5967 ≤ (4237454974949373/100000000000000000000 : ℝ)^1024 := by
      have hnat : (3553 : ℕ)^5967*100000000000000000000^1024 ≤ 4237454974949373^1024*20000^5967 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3553 20000 4237454974949373 100000000000000000000 5967 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3553/20000 : ℝ)) (X := (4237454974949373/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5967 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000088894758056359/50000000000000000000 : ℝ) ≤ (5000001525526483/5000000000000000 : ℝ) ^ (5967/1024 : ℝ) := by
    have hpowers : (50000088894758056359/50000000000000000000 : ℝ)^1024 ≤ (5000001525526483/5000000000000000 : ℝ)^5967 := by
      have hnat : (50000088894758056359 : ℕ)^1024*5000000000000000^5967 ≤ 5000001525526483^5967*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000088894758056359 50000000000000000000 5000001525526483 5000000000000000 1024 5967 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000001525526483/5000000000000000 : ℝ)) (X := (50000088894758056359/50000000000000000000 : ℝ)) (by norm_num) 5967 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25001081587433251433/25000000000000000000 : ℝ) ≤ (5000037121692157/5000000000000000 : ℝ) ^ (5967/1024 : ℝ) := by
    have hpowers : (25001081587433251433/25000000000000000000 : ℝ)^1024 ≤ (5000037121692157/5000000000000000 : ℝ)^5967 := by
      have hnat : (25001081587433251433 : ℕ)^1024*5000000000000000^5967 ≤ 5000037121692157^5967*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25001081587433251433 25000000000000000000 5000037121692157 5000000000000000 1024 5967 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000037121692157/5000000000000000 : ℝ)) (X := (25001081587433251433/25000000000000000000 : ℝ)) (by norm_num) 5967 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50004237454974949373/50000000000000000000 : ℝ) ≤ (5000072717857831/5000000000000000 : ℝ) ^ (5967/1024 : ℝ) := by
    have hpowers : (50004237454974949373/50000000000000000000 : ℝ)^1024 ≤ (5000072717857831/5000000000000000 : ℝ)^5967 := by
      have hnat : (50004237454974949373 : ℕ)^1024*5000000000000000^5967 ≤ 5000072717857831^5967*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50004237454974949373 50000000000000000000 5000072717857831 5000000000000000 1024 5967 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000072717857831/5000000000000000 : ℝ)) (X := (50004237454974949373/50000000000000000000 : ℝ)) (by norm_num) 5967 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(88894758056359/100000000000000000000 : ℝ) ≤ ((5382420189303155419/5382500000000000000 : ℝ)+2*(17798082837/215300000000000 : ℝ)*(9153/100000 : ℝ))^(5967/1024 : ℝ) := by
    rw [show (5382420189303155419/5382500000000000000 : ℝ)+2*(17798082837/215300000000000 : ℝ)*(9153/100000 : ℝ)=(5000001525526483/5000000000000000 : ℝ) by norm_num, show 1+2*(88894758056359/100000000000000000000 : ℝ)=(50000088894758056359/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(4237454974949373/100000000000000000000 : ℝ)+(88894758056359/100000000000000000000 : ℝ) ≤ ((5382420189303155419/5382500000000000000 : ℝ)+(17798082837/215300000000000 : ℝ)*((3553/20000 : ℝ)+(9153/100000 : ℝ)))^(5967/1024 : ℝ) := by
    rw [show (5382420189303155419/5382500000000000000 : ℝ)+(17798082837/215300000000000 : ℝ)*((3553/20000 : ℝ)+(9153/100000 : ℝ))=(5000037121692157/5000000000000000 : ℝ) by norm_num, show 1+(4237454974949373/100000000000000000000 : ℝ)+(88894758056359/100000000000000000000 : ℝ)=(25001081587433251433/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(4237454974949373/100000000000000000000 : ℝ) ≤ ((5382420189303155419/5382500000000000000 : ℝ)+2*(17798082837/215300000000000 : ℝ)*(3553/20000 : ℝ))^(5967/1024 : ℝ) := by
    rw [show (5382420189303155419/5382500000000000000 : ℝ)+2*(17798082837/215300000000000 : ℝ)*(3553/20000 : ℝ)=(5000072717857831/5000000000000000 : ℝ) by norm_num, show 1+2*(4237454974949373/100000000000000000000 : ℝ)=(50004237454974949373/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5382420189303155419/5382500000000000000 : ℝ)*(X 1 0+X 2 0)+(17798082837/215300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5967/1024 : ℝ)) (lo := (9153/100000 : ℝ)) (hi := (3553/20000 : ℝ)) (c := (5382420189303155419/5382500000000000000 : ℝ)) (alpha := (17798082837/215300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5382420189303155419/5382500000000000000 : ℝ)*(X 0 1+X 2 1)+(17798082837/215300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5967/1024 : ℝ)) (lo := (9153/100000 : ℝ)) (hi := (3553/20000 : ℝ)) (c := (5382420189303155419/5382500000000000000 : ℝ)) (alpha := (17798082837/215300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5382420189303155419/5382500000000000000 : ℝ)*(X 0 2+X 1 2)+(17798082837/215300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5967/1024 : ℝ)) (lo := (9153/100000 : ℝ)) (hi := (3553/20000 : ℝ)) (c := (5382420189303155419/5382500000000000000 : ℝ)) (alpha := (17798082837/215300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-576688049/5000000000 : ℝ)*X 0 0+(5480081343/10000000000 : ℝ)*X 0 1+(5084389927/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1763_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2663640867/5000000000 : ℝ)*X 1 0+(-67995909/500000000 : ℝ)*X 1 1+(158887187/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1763_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5327281921/10000000000 : ℝ)*X 2 0+(1271097463/2500000000 : ℝ)*X 2 1+(-1359918107/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1763_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((399478349/1000000000 : ℝ)*X 0 0+(3340258619/10000000000 : ℝ)*X 0 1+(4709493319/10000000000 : ℝ)*X 0 2+(399478349/1000000000 : ℝ)*X 1 0+(3340258619/10000000000 : ℝ)*X 1 1+(4709493319/10000000000 : ℝ)*X 1 2+(399478349/1000000000 : ℝ)*X 2 0+(3340258619/10000000000 : ℝ)*X 2 1+(4709493319/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1763_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-576850849/5000000000 : ℝ)*X 0 0+(1018192273/2000000000 : ℝ)*X 0 1+(2736686547/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1763_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((4080333/7812500 : ℝ)*X 1 0+(-15170859/156250000 : ℝ)*X 1 1+(5473373113/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1763_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1305706567/2500000000 : ℝ)*X 2 0+(5473373087/10000000000 : ℝ)*X 2 1+(-970934973/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1763_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((39959103/100000000 : ℝ)*X 0 0+(4686753903/10000000000 : ℝ)*X 0 1+(420433953/1250000000 : ℝ)*X 0 2+(39959103/100000000 : ℝ)*X 1 0+(4686753903/10000000000 : ℝ)*X 1 1+(420433953/1250000000 : ℝ)*X 1 2+(39959103/100000000 : ℝ)*X 2 0+(4686753903/10000000000 : ℝ)*X 2 1+(420433953/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1763_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (130833603566003059552441209/26912500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (632969563/100000000000000 : ℝ)*(base19) + (2804873/400000000000 : ℝ)*(base23) + (10901239/100000000000000 : ℝ)*(lower2) + (93563729/100000000000000 : ℝ)*(upper3) + (128727319/100000000000000 : ℝ)*(upper5) + (162878551857621/10000000000000 : ℝ)*(major0) + (162878551857621/10000000000000 : ℝ)*(major1) + (162878551857621/10000000000000 : ℝ)*(major2) + (157951671819417/6250000000000 : ℝ)*(sp0) + (4936000156279/195312500000 : ℝ)*(sp1) + (31590400147077/1250000000000 : ℝ)*(sp2) + (365168286269513/50000000000000 : ℝ)*(sp3) + (5963873739/100000000000000 : ℝ)*(sp4) + (1589580847/100000000000000 : ℝ)*(sp7) + (730338162119873/100000000000000 : ℝ)*(f.failure) + (2527232712984411/100000000000000 : ℝ)*(f.sum) + (194800548827/134562500000000000000000000 : ℝ)*base66 + (456068436882073199/53825000000000000000000000000000 : ℝ)*base67 + (269667883204623199/53825000000000000000000000000000 : ℝ)*base69 + (521285815376623199/53825000000000000000000000000000 : ℝ)*base71 + (5098078694419/2153000000000000000000000000 : ℝ)*base73 + (67194218045473199/53825000000000000000000000000000 : ℝ)*base75 + (131140312477023199/53825000000000000000000000000000 : ℝ)*base77 + (884272035441648199/53825000000000000000000000000000 : ℝ)*base79 + (911727709713/538250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (68002619/5000000000000000000000 : ℝ)*base90 + (68002619/5000000000000000000000 : ℝ)*base92 + (68002619/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2156406871639348305733017399/269125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (498070679/50000000000000 : ℝ)*(base19) + (216592991/20000000000000 : ℝ)*(base23) + (28064773/10000000000000 : ℝ)*(lower1) + (43809187/25000000000000 : ℝ)*(upper3) + (394981/1250000000000 : ℝ)*(lower4) + (20531263/12500000000000 : ℝ)*(upper5) + (1685334741711731/100000000000000 : ℝ)*(major0) + (1685334741711731/100000000000000 : ℝ)*(major1) + (1685334741711731/100000000000000 : ℝ)*(major2) + (615194033/100000000000000 : ℝ)*(sp2) + (2614974704208709/100000000000000 : ℝ)*(sp4) + (52299474161347/2000000000000 : ℝ)*(sp5) + (65374325151243/2500000000000 : ℝ)*(sp6) + (755694512126107/100000000000000 : ℝ)*(sp7) + (755694512126107/100000000000000 : ℝ)*(f.failure) + (2614974704208709/100000000000000 : ℝ)*(f.sum) + (20181122895923/10765000000000000000000000000 : ℝ)*base66 + (972065166330195289/538250000000000000000000000000000 : ℝ)*base67 + (6468033644524195289/538250000000000000000000000000000 : ℝ)*base69 + (2052605973784695289/538250000000000000000000000000000 : ℝ)*base71 + (3584721872609/5382500000000000000000000000 : ℝ)*base74 + (12775201444946195289/538250000000000000000000000000000 : ℝ)*base75 + (4651945290282445289/538250000000000000000000000000000 : ℝ)*base77 + (4410131136189445289/538250000000000000000000000000000 : ℝ)*base79 + (12819186131471/5382500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (20915321/5000000000000000000000 : ℝ)*base90 + (20915321/5000000000000000000000 : ℝ)*base92 + (20915321/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1763_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5967/1024 : ℝ) ≤ p) (hpb : p ≤ (5983/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (111508997/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3553/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9153/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4593/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (709/4000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1763_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1763_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5967/1024 : ℝ) ≤ p) (hpb : p ≤ (5983/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (111508997/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4593/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (709/4000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1763_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1763_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1763_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5967/1024 : ℝ) ≤ p) (hpb : p ≤ (5983/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (111508997/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4593/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (709/4000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1763_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
