-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1451_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:59:38.566535+00:00
-- url     : https://prove2.me/submissions/5092e0f3-89ad-4a36-a058-5a29e8e066dc

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
theorem support_rectangle_w1451_s6_0 (p : ℝ) (hpa : (2205/512 : ℝ) ≤ p) (hpb : p ≤ (4411/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-7813679/40000000 : ℝ)*x 0 + (2703543587/5000000000 : ℝ)*x 1 + (2623687229/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7813679/40000000 : ℝ)^4411 ≤ (2980712392179/25000000000000 : ℝ)^3387 := by
    have hnat : (7813679 : ℕ)^4411*25000000000000^3387 ≤ 2980712392179^3387*40000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7813679 40000000 2980712392179 25000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2703543587/5000000000 : ℝ)^4411 ≤ (44898262411433/100000000000000 : ℝ)^3387 := by
    have hnat : (2703543587 : ℕ)^4411*100000000000000^3387 ≤ 44898262411433^3387*5000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2703543587 5000000000 44898262411433 100000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2623687229/5000000000 : ℝ)^4411 ≤ (21589444000627/50000000000000 : ℝ)^3387 := by
    have hnat : (2623687229 : ℕ)^4411*50000000000000^3387 ≤ 21589444000627^3387*5000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623687229 5000000000 21589444000627 50000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4411/1024 : ℝ)) 4411 3387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-7813679/40000000 : ℝ), (2703543587/5000000000 : ℝ), (2623687229/5000000000 : ℝ)] ![(2980712392179/25000000000000 : ℝ), (44898262411433/100000000000000 : ℝ), (21589444000627/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-7813679/40000000 : ℝ)|^4411 ≤ (2980712392179/25000000000000 : ℝ)^3387
        have hw : |(-7813679/40000000 : ℝ)|=(7813679/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2703543587/5000000000 : ℝ)|^4411 ≤ (44898262411433/100000000000000 : ℝ)^3387
        have hw : |(2703543587/5000000000 : ℝ)|=(2703543587/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2623687229/5000000000 : ℝ)|^4411 ≤ (21589444000627/50000000000000 : ℝ)^3387
        have hw : |(2623687229/5000000000 : ℝ)|=(2623687229/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1451_s6_1 (p : ℝ) (hpa : (2205/512 : ℝ) ≤ p) (hpb : p ≤ (4411/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5346855197/10000000000 : ℝ)*x 0 + (-2034717279/10000000000 : ℝ)*x 1 + (2623687211/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5346855197/10000000000 : ℝ)^4411 ≤ (44248010995497/100000000000000 : ℝ)^3387 := by
    have hnat : (5346855197 : ℕ)^4411*100000000000000^3387 ≤ 44248010995497^3387*10000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5346855197 10000000000 44248010995497 100000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2034717279/10000000000 : ℝ)^4411 ≤ (1571637671477/12500000000000 : ℝ)^3387 := by
    have hnat : (2034717279 : ℕ)^4411*12500000000000^3387 ≤ 1571637671477^3387*10000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2034717279 10000000000 1571637671477 12500000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2623687211/5000000000 : ℝ)^4411 ≤ (43178887615461/100000000000000 : ℝ)^3387 := by
    have hnat : (2623687211 : ℕ)^4411*100000000000000^3387 ≤ 43178887615461^3387*5000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623687211 5000000000 43178887615461 100000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4411/1024 : ℝ)) 4411 3387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5346855197/10000000000 : ℝ), (-2034717279/10000000000 : ℝ), (2623687211/5000000000 : ℝ)] ![(44248010995497/100000000000000 : ℝ), (1571637671477/12500000000000 : ℝ), (43178887615461/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5346855197/10000000000 : ℝ)|^4411 ≤ (44248010995497/100000000000000 : ℝ)^3387
        have hw : |(5346855197/10000000000 : ℝ)|=(5346855197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2034717279/10000000000 : ℝ)|^4411 ≤ (1571637671477/12500000000000 : ℝ)^3387
        have hw : |(-2034717279/10000000000 : ℝ)|=(2034717279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2623687211/5000000000 : ℝ)|^4411 ≤ (43178887615461/100000000000000 : ℝ)^3387
        have hw : |(2623687211/5000000000 : ℝ)|=(2623687211/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1451_s6_2 (p : ℝ) (hpa : (2205/512 : ℝ) ≤ p) (hpb : p ≤ (4411/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5346855389/10000000000 : ℝ)*x 0 + (5247374463/10000000000 : ℝ)*x 1 + (-254339621/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5346855389/10000000000 : ℝ)^4411 ≤ (44248013064773/100000000000000 : ℝ)^3387 := by
    have hnat : (5346855389 : ℕ)^4411*100000000000000^3387 ≤ 44248013064773^3387*10000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5346855389 10000000000 44248013064773 100000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5247374463/10000000000 : ℝ)^4411 ≤ (10794722013709/25000000000000 : ℝ)^3387 := by
    have hnat : (5247374463 : ℕ)^4411*25000000000000^3387 ≤ 10794722013709^3387*10000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5247374463 10000000000 10794722013709 25000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (254339621/1250000000 : ℝ)^4411 ≤ (1571637358631/12500000000000 : ℝ)^3387 := by
    have hnat : (254339621 : ℕ)^4411*12500000000000^3387 ≤ 1571637358631^3387*1250000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      254339621 1250000000 1571637358631 12500000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4411/1024 : ℝ)) 4411 3387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5346855389/10000000000 : ℝ), (5247374463/10000000000 : ℝ), (-254339621/1250000000 : ℝ)] ![(44248013064773/100000000000000 : ℝ), (10794722013709/25000000000000 : ℝ), (1571637358631/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5346855389/10000000000 : ℝ)|^4411 ≤ (44248013064773/100000000000000 : ℝ)^3387
        have hw : |(5346855389/10000000000 : ℝ)|=(5346855389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5247374463/10000000000 : ℝ)|^4411 ≤ (10794722013709/25000000000000 : ℝ)^3387
        have hw : |(5247374463/10000000000 : ℝ)|=(5247374463/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-254339621/1250000000 : ℝ)|^4411 ≤ (1571637358631/12500000000000 : ℝ)^3387
        have hw : |(-254339621/1250000000 : ℝ)|=(254339621/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1451_s6_3 (p : ℝ) (hpa : (2205/512 : ℝ) ≤ p) (hpb : p ≤ (4411/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2149451331/5000000000 : ℝ)*x 0 + (1031973869/2500000000 : ℝ)*x 1 + (1119048761/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2149451331/5000000000 : ℝ)^4411 ≤ (6661004341567/20000000000000 : ℝ)^3387 := by
    have hnat : (2149451331 : ℕ)^4411*20000000000000^3387 ≤ 6661004341567^3387*5000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2149451331 5000000000 6661004341567 20000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1031973869/2500000000 : ℝ)^4411 ≤ (6318020087217/20000000000000 : ℝ)^3387 := by
    have hnat : (1031973869 : ℕ)^4411*20000000000000^3387 ≤ 6318020087217^3387*2500000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1031973869 2500000000 6318020087217 20000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1119048761/2500000000 : ℝ)^4411 ≤ (8776219462339/25000000000000 : ℝ)^3387 := by
    have hnat : (1119048761 : ℕ)^4411*25000000000000^3387 ≤ 8776219462339^3387*2500000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1119048761 2500000000 8776219462339 25000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4411/1024 : ℝ)) 4411 3387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2149451331/5000000000 : ℝ), (1031973869/2500000000 : ℝ), (1119048761/2500000000 : ℝ)] ![(6661004341567/20000000000000 : ℝ), (6318020087217/20000000000000 : ℝ), (8776219462339/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2149451331/5000000000 : ℝ)|^4411 ≤ (6661004341567/20000000000000 : ℝ)^3387
        have hw : |(2149451331/5000000000 : ℝ)|=(2149451331/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1031973869/2500000000 : ℝ)|^4411 ≤ (6318020087217/20000000000000 : ℝ)^3387
        have hw : |(1031973869/2500000000 : ℝ)|=(1031973869/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1119048761/2500000000 : ℝ)|^4411 ≤ (8776219462339/25000000000000 : ℝ)^3387
        have hw : |(1119048761/2500000000 : ℝ)|=(1119048761/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1451_s6_4 (p : ℝ) (hpa : (2205/512 : ℝ) ≤ p) (hpb : p ≤ (4411/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1953430629/10000000000 : ℝ)*x 0 + (1049590351/2000000000 : ℝ)*x 1 + (5406507071/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1953430629/10000000000 : ℝ)^4411 ≤ (186295875699/1562500000000 : ℝ)^3387 := by
    have hnat : (1953430629 : ℕ)^4411*1562500000000^3387 ≤ 186295875699^3387*10000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1953430629 10000000000 186295875699 1562500000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1049590351/2000000000 : ℝ)^4411 ≤ (674766791923/1562500000000 : ℝ)^3387 := by
    have hnat : (1049590351 : ℕ)^4411*1562500000000^3387 ≤ 674766791923^3387*2000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049590351 2000000000 674766791923 1562500000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5406507071/10000000000 : ℝ)^4411 ≤ (22445994627689/50000000000000 : ℝ)^3387 := by
    have hnat : (5406507071 : ℕ)^4411*50000000000000^3387 ≤ 22445994627689^3387*10000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406507071 10000000000 22445994627689 50000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4411/1024 : ℝ)) 4411 3387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1953430629/10000000000 : ℝ), (1049590351/2000000000 : ℝ), (5406507071/10000000000 : ℝ)] ![(186295875699/1562500000000 : ℝ), (674766791923/1562500000000 : ℝ), (22445994627689/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1953430629/10000000000 : ℝ)|^4411 ≤ (186295875699/1562500000000 : ℝ)^3387
        have hw : |(-1953430629/10000000000 : ℝ)|=(1953430629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1049590351/2000000000 : ℝ)|^4411 ≤ (674766791923/1562500000000 : ℝ)^3387
        have hw : |(1049590351/2000000000 : ℝ)|=(1049590351/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5406507071/10000000000 : ℝ)|^4411 ≤ (22445994627689/50000000000000 : ℝ)^3387
        have hw : |(5406507071/10000000000 : ℝ)|=(5406507071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1451_s6_5 (p : ℝ) (hpa : (2205/512 : ℝ) ≤ p) (hpb : p ≤ (4411/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1326311613/2500000000 : ℝ)*x 0 + (-937792259/5000000000 : ℝ)*x 1 + (1081301429/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1326311613/2500000000 : ℝ)^4411 ≤ (2190005104793/5000000000000 : ℝ)^3387 := by
    have hnat : (1326311613 : ℕ)^4411*5000000000000^3387 ≤ 2190005104793^3387*2500000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1326311613 2500000000 2190005104793 5000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (937792259/5000000000 : ℝ)^4411 ≤ (176686059981/1562500000000 : ℝ)^3387 := by
    have hnat : (937792259 : ℕ)^4411*1562500000000^3387 ≤ 176686059981^3387*5000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      937792259 5000000000 176686059981 1562500000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1081301429/2000000000 : ℝ)^4411 ≤ (44891990055591/100000000000000 : ℝ)^3387 := by
    have hnat : (1081301429 : ℕ)^4411*100000000000000^3387 ≤ 44891990055591^3387*2000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081301429 2000000000 44891990055591 100000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4411/1024 : ℝ)) 4411 3387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1326311613/2500000000 : ℝ), (-937792259/5000000000 : ℝ), (1081301429/2000000000 : ℝ)] ![(2190005104793/5000000000000 : ℝ), (176686059981/1562500000000 : ℝ), (44891990055591/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1326311613/2500000000 : ℝ)|^4411 ≤ (2190005104793/5000000000000 : ℝ)^3387
        have hw : |(1326311613/2500000000 : ℝ)|=(1326311613/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-937792259/5000000000 : ℝ)|^4411 ≤ (176686059981/1562500000000 : ℝ)^3387
        have hw : |(-937792259/5000000000 : ℝ)|=(937792259/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1081301429/2000000000 : ℝ)|^4411 ≤ (44891990055591/100000000000000 : ℝ)^3387
        have hw : |(1081301429/2000000000 : ℝ)|=(1081301429/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1451_s6_6 (p : ℝ) (hpa : (2205/512 : ℝ) ≤ p) (hpb : p ≤ (4411/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305246247/10000000000 : ℝ)*x 0 + (1081301481/2000000000 : ℝ)*x 1 + (-1875584441/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305246247/10000000000 : ℝ)^4411 ≤ (43800099891689/100000000000000 : ℝ)^3387 := by
    have hnat : (5305246247 : ℕ)^4411*100000000000000^3387 ≤ 43800099891689^3387*10000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305246247 10000000000 43800099891689 100000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1081301481/2000000000 : ℝ)^4411 ≤ (44891992867151/100000000000000 : ℝ)^3387 := by
    have hnat : (1081301481 : ℕ)^4411*100000000000000^3387 ≤ 44891992867151^3387*2000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081301481 2000000000 44891992867151 100000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1875584441/10000000000 : ℝ)^4411 ≤ (5653953617099/50000000000000 : ℝ)^3387 := by
    have hnat : (1875584441 : ℕ)^4411*50000000000000^3387 ≤ 5653953617099^3387*10000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1875584441 10000000000 5653953617099 50000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4411/1024 : ℝ)) 4411 3387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305246247/10000000000 : ℝ), (1081301481/2000000000 : ℝ), (-1875584441/10000000000 : ℝ)] ![(43800099891689/100000000000000 : ℝ), (44891992867151/100000000000000 : ℝ), (5653953617099/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305246247/10000000000 : ℝ)|^4411 ≤ (43800099891689/100000000000000 : ℝ)^3387
        have hw : |(5305246247/10000000000 : ℝ)|=(5305246247/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1081301481/2000000000 : ℝ)|^4411 ≤ (44891992867151/100000000000000 : ℝ)^3387
        have hw : |(1081301481/2000000000 : ℝ)|=(1081301481/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1875584441/10000000000 : ℝ)|^4411 ≤ (5653953617099/50000000000000 : ℝ)^3387
        have hw : |(-1875584441/10000000000 : ℝ)|=(1875584441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1451_s6_7 (p : ℝ) (hpa : (2205/512 : ℝ) ≤ p) (hpb : p ≤ (4411/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2149463331/5000000000 : ℝ)*x 0 + (4474936399/10000000000 : ℝ)*x 1 + (1032290229/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2149463331/5000000000 : ℝ)^4411 ≤ (33305263858451/100000000000000 : ℝ)^3387 := by
    have hnat : (2149463331 : ℕ)^4411*100000000000000^3387 ≤ 33305263858451^3387*5000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2149463331 5000000000 33305263858451 100000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4474936399/10000000000 : ℝ)^4411 ≤ (35092023055441/100000000000000 : ℝ)^3387 := by
    have hnat : (4474936399 : ℕ)^4411*100000000000000^3387 ≤ 35092023055441^3387*10000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4474936399 10000000000 35092023055441 100000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1032290229/2500000000 : ℝ)^4411 ≤ (7900678267991/25000000000000 : ℝ)^3387 := by
    have hnat : (1032290229 : ℕ)^4411*25000000000000^3387 ≤ 7900678267991^3387*2500000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1032290229 2500000000 7900678267991 25000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4411/1024 : ℝ)) 4411 3387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2149463331/5000000000 : ℝ), (4474936399/10000000000 : ℝ), (1032290229/2500000000 : ℝ)] ![(33305263858451/100000000000000 : ℝ), (35092023055441/100000000000000 : ℝ), (7900678267991/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2149463331/5000000000 : ℝ)|^4411 ≤ (33305263858451/100000000000000 : ℝ)^3387
        have hw : |(2149463331/5000000000 : ℝ)|=(2149463331/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4474936399/10000000000 : ℝ)|^4411 ≤ (35092023055441/100000000000000 : ℝ)^3387
        have hw : |(4474936399/10000000000 : ℝ)|=(4474936399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1032290229/2500000000 : ℝ)|^4411 ≤ (7900678267991/25000000000000 : ℝ)^3387
        have hw : |(1032290229/2500000000 : ℝ)|=(1032290229/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1451_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2205/512 : ℝ) ≤ p) (hpb : p ≤ (4411/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (159039209/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14771/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11381/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1423/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (923/6250 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14771/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11381/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14771/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11381/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14771/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11381/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14771/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11381/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14771/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11381/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14771/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11381/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11381/100000 : ℝ) ^ (2205/512 : ℝ) ≤ (8616051149350133/100000000000000000000 : ℝ) := by
    have hpowers : (11381/100000 : ℝ)^2205 ≤ (8616051149350133/100000000000000000000 : ℝ)^512 := by
      have hnat : (11381 : ℕ)^2205*100000000000000000000^512 ≤ 8616051149350133^512*100000^2205 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11381 100000 8616051149350133 100000000000000000000 2205 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11381/100000 : ℝ)) (X := (8616051149350133/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2205 512 (by norm_num) hpowers
    exact h
  have hpowhi : (14771/100000 : ℝ) ^ (2205/512 : ℝ) ≤ (6620441208968477/25000000000000000000 : ℝ) := by
    have hpowers : (14771/100000 : ℝ)^2205 ≤ (6620441208968477/25000000000000000000 : ℝ)^512 := by
      have hnat : (14771 : ℕ)^2205*25000000000000000000^512 ≤ 6620441208968477^512*100000^2205 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14771 100000 6620441208968477 25000000000000000000 2205 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14771/100000 : ℝ)) (X := (6620441208968477/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2205 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50008616051149350133/50000000000000000000 : ℝ) ≤ (10000400102166421/10000000000000000 : ℝ) ^ (2205/512 : ℝ) := by
    have hpowers : (50008616051149350133/50000000000000000000 : ℝ)^512 ≤ (10000400102166421/10000000000000000 : ℝ)^2205 := by
      have hnat : (50008616051149350133 : ℕ)^512*10000000000000000^2205 ≤ 10000400102166421^2205*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50008616051149350133 50000000000000000000 10000400102166421 10000000000000000 512 2205 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000400102166421/10000000000000000 : ℝ)) (X := (50008616051149350133/50000000000000000000 : ℝ)) (by norm_num) 2205 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100035097815985224041/100000000000000000000 : ℝ) ≤ (10000814859908643/10000000000000000 : ℝ) ^ (2205/512 : ℝ) := by
    have hpowers : (100035097815985224041/100000000000000000000 : ℝ)^512 ≤ (10000814859908643/10000000000000000 : ℝ)^2205 := by
      have hnat : (100035097815985224041 : ℕ)^512*10000000000000000^2205 ≤ 10000814859908643^2205*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100035097815985224041 100000000000000000000 10000814859908643 10000000000000000 512 2205 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000814859908643/10000000000000000 : ℝ)) (X := (100035097815985224041/100000000000000000000 : ℝ)) (by norm_num) 2205 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (12506620441208968477/12500000000000000000 : ℝ) ≤ (2000245923530173/2000000000000000 : ℝ) ^ (2205/512 : ℝ) := by
    have hpowers : (12506620441208968477/12500000000000000000 : ℝ)^512 ≤ (2000245923530173/2000000000000000 : ℝ)^2205 := by
      have hnat : (12506620441208968477 : ℕ)^512*2000000000000000^2205 ≤ 2000245923530173^2205*12500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12506620441208968477 12500000000000000000 2000245923530173 2000000000000000 512 2205 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000245923530173/2000000000000000 : ℝ)) (X := (12506620441208968477/12500000000000000000 : ℝ)) (by norm_num) 2205 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(8616051149350133/100000000000000000000 : ℝ) ≤ ((16945957815307855013/16950000000000000000 : ℝ)+2*(207378871111/169500000000000 : ℝ)*(11381/100000 : ℝ))^(2205/512 : ℝ) := by
    rw [show (16945957815307855013/16950000000000000000 : ℝ)+2*(207378871111/169500000000000 : ℝ)*(11381/100000 : ℝ)=(10000400102166421/10000000000000000 : ℝ) by norm_num, show 1+2*(8616051149350133/100000000000000000000 : ℝ)=(50008616051149350133/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(6620441208968477/25000000000000000000 : ℝ)+(8616051149350133/100000000000000000000 : ℝ) ≤ ((16945957815307855013/16950000000000000000 : ℝ)+(207378871111/169500000000000 : ℝ)*((14771/100000 : ℝ)+(11381/100000 : ℝ)))^(2205/512 : ℝ) := by
    rw [show (16945957815307855013/16950000000000000000 : ℝ)+(207378871111/169500000000000 : ℝ)*((14771/100000 : ℝ)+(11381/100000 : ℝ))=(10000814859908643/10000000000000000 : ℝ) by norm_num, show 1+(6620441208968477/25000000000000000000 : ℝ)+(8616051149350133/100000000000000000000 : ℝ)=(100035097815985224041/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(6620441208968477/25000000000000000000 : ℝ) ≤ ((16945957815307855013/16950000000000000000 : ℝ)+2*(207378871111/169500000000000 : ℝ)*(14771/100000 : ℝ))^(2205/512 : ℝ) := by
    rw [show (16945957815307855013/16950000000000000000 : ℝ)+2*(207378871111/169500000000000 : ℝ)*(14771/100000 : ℝ)=(2000245923530173/2000000000000000 : ℝ) by norm_num, show 1+2*(6620441208968477/25000000000000000000 : ℝ)=(12506620441208968477/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (16945957815307855013/16950000000000000000 : ℝ)*(X 1 0+X 2 0)+(207378871111/169500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2205/512 : ℝ)) (lo := (11381/100000 : ℝ)) (hi := (14771/100000 : ℝ)) (c := (16945957815307855013/16950000000000000000 : ℝ)) (alpha := (207378871111/169500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (16945957815307855013/16950000000000000000 : ℝ)*(X 0 1+X 2 1)+(207378871111/169500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2205/512 : ℝ)) (lo := (11381/100000 : ℝ)) (hi := (14771/100000 : ℝ)) (c := (16945957815307855013/16950000000000000000 : ℝ)) (alpha := (207378871111/169500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (16945957815307855013/16950000000000000000 : ℝ)*(X 0 2+X 1 2)+(207378871111/169500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2205/512 : ℝ)) (lo := (11381/100000 : ℝ)) (hi := (14771/100000 : ℝ)) (c := (16945957815307855013/16950000000000000000 : ℝ)) (alpha := (207378871111/169500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-7813679/40000000 : ℝ)*X 0 0+(2703543587/5000000000 : ℝ)*X 0 1+(2623687229/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1451_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5346855197/10000000000 : ℝ)*X 1 0+(-2034717279/10000000000 : ℝ)*X 1 1+(2623687211/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1451_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5346855389/10000000000 : ℝ)*X 2 0+(5247374463/10000000000 : ℝ)*X 2 1+(-254339621/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1451_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2149451331/5000000000 : ℝ)*X 0 0+(1031973869/2500000000 : ℝ)*X 0 1+(1119048761/2500000000 : ℝ)*X 0 2+(2149451331/5000000000 : ℝ)*X 1 0+(1031973869/2500000000 : ℝ)*X 1 1+(1119048761/2500000000 : ℝ)*X 1 2+(2149451331/5000000000 : ℝ)*X 2 0+(1031973869/2500000000 : ℝ)*X 2 1+(1119048761/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1451_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1953430629/10000000000 : ℝ)*X 0 0+(1049590351/2000000000 : ℝ)*X 0 1+(5406507071/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1451_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1326311613/2500000000 : ℝ)*X 1 0+(-937792259/5000000000 : ℝ)*X 1 1+(1081301429/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1451_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305246247/10000000000 : ℝ)*X 2 0+(1081301481/2000000000 : ℝ)*X 2 1+(-1875584441/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1451_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2149463331/5000000000 : ℝ)*X 0 0+(4474936399/10000000000 : ℝ)*X 0 1+(1032290229/2500000000 : ℝ)*X 0 2+(2149463331/5000000000 : ℝ)*X 1 0+(4474936399/10000000000 : ℝ)*X 1 1+(1032290229/2500000000 : ℝ)*X 1 2+(2149463331/5000000000 : ℝ)*X 2 0+(4474936399/10000000000 : ℝ)*X 2 1+(1032290229/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1451_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (72414309081762162068139761/8828125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (920688297/50000000000000 : ℝ)*(base19) + (1002924301/50000000000000 : ℝ)*(base23) + (67307337/100000000000000 : ℝ)*(upper3) + (32276549/100000000000000 : ℝ)*(upper4) + (462476627/100000000000000 : ℝ)*(upper5) + (142694626895551/3125000000000 : ℝ)*(major0) + (142694626895551/3125000000000 : ℝ)*(major1) + (142694626895551/3125000000000 : ℝ)*(major2) + (1252254593302543/20000000000000 : ℝ)*(sp0) + (1565330118309703/25000000000000 : ℝ)*(sp1) + (1565330077191701/25000000000000 : ℝ)*(sp2) + (574222989609987/20000000000000 : ℝ)*(sp3) + (4934810269/10000000000000 : ℝ)*(sp4) + (1161576697/6250000000000 : ℝ)*(sp7) + (89722922914909/3125000000000 : ℝ)*(f.failure) + (3130661157307703/50000000000000 : ℝ)*(f.sum) + (12026231069251/4237500000000000000000000000 : ℝ)*base65 + (52574337726490721/17656250000000000000000000000000 : ℝ)*base67 + (332942702830865721/17656250000000000000000000000000 : ℝ)*base69 + (218191348918678221/17656250000000000000000000000000 : ℝ)*base71 + (656259713981/1059375000000000000000000000 : ℝ)*base74 + (268601346728990721/17656250000000000000000000000000 : ℝ)*base75 + (243838803684928221/17656250000000000000000000000000 : ℝ)*base77 + (23590051508365721/17656250000000000000000000000000 : ℝ)*base79 + (15062629924163/2118750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1666981/312500000000000000000 : ℝ)*base89 + (1666981/312500000000000000000 : ℝ)*base91 + (1666981/312500000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (9657041356062686209236623/1250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (926929483/100000000000000 : ℝ)*(base19) + (830596201/100000000000000 : ℝ)*(base23) + (267245587/100000000000000 : ℝ)*(lower1) + (51302507/25000000000000 : ℝ)*(upper3) + (43605753/100000000000000 : ℝ)*(lower4) + (65315997/100000000000000 : ℝ)*(upper5) + (4599482972528723/100000000000000 : ℝ)*(major0) + (4599482972528723/100000000000000 : ℝ)*(major1) + (4599482972528723/100000000000000 : ℝ)*(major2) + (4155210793/50000000000000 : ℝ)*(sp2) + (6306922271671041/100000000000000 : ℝ)*(sp4) + (3153460672370779/50000000000000 : ℝ)*(sp5) + (1261382626130651/20000000000000 : ℝ)*(sp6) + (2892043415865281/100000000000000 : ℝ)*(sp7) + (2892043415865281/100000000000000 : ℝ)*(f.failure) + (6306922271671041/100000000000000 : ℝ)*(f.sum) + (19881808189211/4237500000000000000000000000 : ℝ)*base66 + (29449840026547553867/565000000000000000000000000000000 : ℝ)*base68 + (2736798471807446133/565000000000000000000000000000000 : ℝ)*base69 + (28447012579207553867/565000000000000000000000000000000 : ℝ)*base72 + (4165824846407/2118750000000000000000000000 : ℝ)*base73 + (28537647092627553867/565000000000000000000000000000000 : ℝ)*base76 + (2613324757702553867/565000000000000000000000000000000 : ℝ)*base78 + (16108260347017553867/565000000000000000000000000000000 : ℝ)*base80 + (73925725961/4237500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (40802729/10000000000000000000000 : ℝ)*base89 + (40802729/10000000000000000000000 : ℝ)*base91 + (40802729/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1451_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2205/512 : ℝ) ≤ p) (hpb : p ≤ (4411/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (159039209/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14771/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11381/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1423/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (923/6250 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1451_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1451_s7_0 (p : ℝ) (hpa : (2205/512 : ℝ) ≤ p) (hpb : p ≤ (4411/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1953423733/10000000000 : ℝ)*x 0 + (540706421/1000000000 : ℝ)*x 1 + (5247394677/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1953423733/10000000000 : ℝ)^4411 ≤ (1490360153643/12500000000000 : ℝ)^3387 := by
    have hnat : (1953423733 : ℕ)^4411*12500000000000^3387 ≤ 1490360153643^3387*10000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1953423733 10000000000 1490360153643 12500000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (540706421/1000000000 : ℝ)^4411 ≤ (11224503519487/25000000000000 : ℝ)^3387 := by
    have hnat : (540706421 : ℕ)^4411*25000000000000^3387 ≤ 11224503519487^3387*1000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540706421 1000000000 11224503519487 25000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5247394677/10000000000 : ℝ)^4411 ≤ (134934702117/312500000000 : ℝ)^3387 := by
    have hnat : (5247394677 : ℕ)^4411*312500000000^3387 ≤ 134934702117^3387*10000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5247394677 10000000000 134934702117 312500000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4411/1024 : ℝ)) 4411 3387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1953423733/10000000000 : ℝ), (540706421/1000000000 : ℝ), (5247394677/10000000000 : ℝ)] ![(1490360153643/12500000000000 : ℝ), (11224503519487/25000000000000 : ℝ), (134934702117/312500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1953423733/10000000000 : ℝ)|^4411 ≤ (1490360153643/12500000000000 : ℝ)^3387
        have hw : |(-1953423733/10000000000 : ℝ)|=(1953423733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(540706421/1000000000 : ℝ)|^4411 ≤ (11224503519487/25000000000000 : ℝ)^3387
        have hw : |(540706421/1000000000 : ℝ)|=(540706421/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5247394677/10000000000 : ℝ)|^4411 ≤ (134934702117/312500000000 : ℝ)^3387
        have hw : |(5247394677/10000000000 : ℝ)|=(5247394677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1451_s7_1 (p : ℝ) (hpa : (2205/512 : ℝ) ≤ p) (hpb : p ≤ (4411/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1069370371/2000000000 : ℝ)*x 0 + (-2034699197/10000000000 : ℝ)*x 1 + (2623695681/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069370371/2000000000 : ℝ)^4411 ≤ (8849594995433/20000000000000 : ℝ)^3387 := by
    have hnat : (1069370371 : ℕ)^4411*20000000000000^3387 ≤ 8849594995433^3387*2000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069370371 2000000000 8849594995433 20000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2034699197/10000000000 : ℝ)^4411 ≤ (6286477928689/50000000000000 : ℝ)^3387 := by
    have hnat : (2034699197 : ℕ)^4411*50000000000000^3387 ≤ 6286477928689^3387*10000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2034699197 10000000000 6286477928689 50000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2623695681/5000000000 : ℝ)^4411 ≤ (5397383644043/12500000000000 : ℝ)^3387 := by
    have hnat : (2623695681 : ℕ)^4411*12500000000000^3387 ≤ 5397383644043^3387*5000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623695681 5000000000 5397383644043 12500000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4411/1024 : ℝ)) 4411 3387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069370371/2000000000 : ℝ), (-2034699197/10000000000 : ℝ), (2623695681/5000000000 : ℝ)] ![(8849594995433/20000000000000 : ℝ), (6286477928689/50000000000000 : ℝ), (5397383644043/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069370371/2000000000 : ℝ)|^4411 ≤ (8849594995433/20000000000000 : ℝ)^3387
        have hw : |(1069370371/2000000000 : ℝ)|=(1069370371/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2034699197/10000000000 : ℝ)|^4411 ≤ (6286477928689/50000000000000 : ℝ)^3387
        have hw : |(-2034699197/10000000000 : ℝ)|=(2034699197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2623695681/5000000000 : ℝ)|^4411 ≤ (5397383644043/12500000000000 : ℝ)^3387
        have hw : |(2623695681/5000000000 : ℝ)|=(2623695681/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1451_s7_2 (p : ℝ) (hpa : (2205/512 : ℝ) ≤ p) (hpb : p ≤ (4411/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5346850779/10000000000 : ℝ)*x 0 + (262369659/500000000 : ℝ)*x 1 + (-254337277/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5346850779/10000000000 : ℝ)^4411 ≤ (221239816903/500000000000 : ℝ)^3387 := by
    have hnat : (5346850779 : ℕ)^4411*500000000000^3387 ≤ 221239816903^3387*10000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5346850779 10000000000 221239816903 500000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (262369659/500000000 : ℝ)^4411 ≤ (8635817726977/20000000000000 : ℝ)^3387 := by
    have hnat : (262369659 : ℕ)^4411*20000000000000^3387 ≤ 8635817726977^3387*500000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262369659 500000000 8635817726977 20000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (254337277/1250000000 : ℝ)^4411 ≤ (196452311919/1562500000000 : ℝ)^3387 := by
    have hnat : (254337277 : ℕ)^4411*1562500000000^3387 ≤ 196452311919^3387*1250000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      254337277 1250000000 196452311919 1562500000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4411/1024 : ℝ)) 4411 3387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5346850779/10000000000 : ℝ), (262369659/500000000 : ℝ), (-254337277/1250000000 : ℝ)] ![(221239816903/500000000000 : ℝ), (8635817726977/20000000000000 : ℝ), (196452311919/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5346850779/10000000000 : ℝ)|^4411 ≤ (221239816903/500000000000 : ℝ)^3387
        have hw : |(5346850779/10000000000 : ℝ)|=(5346850779/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(262369659/500000000 : ℝ)|^4411 ≤ (8635817726977/20000000000000 : ℝ)^3387
        have hw : |(262369659/500000000 : ℝ)|=(262369659/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-254337277/1250000000 : ℝ)|^4411 ≤ (196452311919/1562500000000 : ℝ)^3387
        have hw : |(-254337277/1250000000 : ℝ)|=(254337277/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1451_s7_3 (p : ℝ) (hpa : (2205/512 : ℝ) ≤ p) (hpb : p ≤ (4411/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2149451071/5000000000 : ℝ)*x 0 + (4127941441/10000000000 : ℝ)*x 1 + (279759419/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2149451071/5000000000 : ℝ)^4411 ≤ (33305016461243/100000000000000 : ℝ)^3387 := by
    have hnat : (2149451071 : ℕ)^4411*100000000000000^3387 ≤ 33305016461243^3387*5000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2149451071 5000000000 33305016461243 100000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4127941441/10000000000 : ℝ)^4411 ≤ (3948819818577/12500000000000 : ℝ)^3387 := by
    have hnat : (4127941441 : ℕ)^4411*12500000000000^3387 ≤ 3948819818577^3387*10000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4127941441 10000000000 3948819818577 12500000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (279759419/625000000 : ℝ)^4411 ≤ (35104424977467/100000000000000 : ℝ)^3387 := by
    have hnat : (279759419 : ℕ)^4411*100000000000000^3387 ≤ 35104424977467^3387*625000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      279759419 625000000 35104424977467 100000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4411/1024 : ℝ)) 4411 3387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2149451071/5000000000 : ℝ), (4127941441/10000000000 : ℝ), (279759419/625000000 : ℝ)] ![(33305016461243/100000000000000 : ℝ), (3948819818577/12500000000000 : ℝ), (35104424977467/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2149451071/5000000000 : ℝ)|^4411 ≤ (33305016461243/100000000000000 : ℝ)^3387
        have hw : |(2149451071/5000000000 : ℝ)|=(2149451071/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4127941441/10000000000 : ℝ)|^4411 ≤ (3948819818577/12500000000000 : ℝ)^3387
        have hw : |(4127941441/10000000000 : ℝ)|=(4127941441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(279759419/625000000 : ℝ)|^4411 ≤ (35104424977467/100000000000000 : ℝ)^3387
        have hw : |(279759419/625000000 : ℝ)|=(279759419/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1451_s7_4 (p : ℝ) (hpa : (2205/512 : ℝ) ≤ p) (hpb : p ≤ (4411/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2652625973/5000000000 : ℝ)*x 0 + (-1875606063/10000000000 : ℝ)*x 1 + (2703243019/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652625973/5000000000 : ℝ)^4411 ≤ (10950040291913/25000000000000 : ℝ)^3387 := by
    have hnat : (2652625973 : ℕ)^4411*25000000000000^3387 ≤ 10950040291913^3387*5000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652625973 5000000000 10950040291913 25000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1875606063/10000000000 : ℝ)^4411 ≤ (11308077005429/100000000000000 : ℝ)^3387 := by
    have hnat : (1875606063 : ℕ)^4411*100000000000000^3387 ≤ 11308077005429^3387*10000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1875606063 10000000000 11308077005429 100000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2703243019/5000000000 : ℝ)^4411 ≤ (44891761811159/100000000000000 : ℝ)^3387 := by
    have hnat : (2703243019 : ℕ)^4411*100000000000000^3387 ≤ 44891761811159^3387*5000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2703243019 5000000000 44891761811159 100000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4411/1024 : ℝ)) 4411 3387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652625973/5000000000 : ℝ), (-1875606063/10000000000 : ℝ), (2703243019/5000000000 : ℝ)] ![(10950040291913/25000000000000 : ℝ), (11308077005429/100000000000000 : ℝ), (44891761811159/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652625973/5000000000 : ℝ)|^4411 ≤ (10950040291913/25000000000000 : ℝ)^3387
        have hw : |(2652625973/5000000000 : ℝ)|=(2652625973/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1875606063/10000000000 : ℝ)|^4411 ≤ (11308077005429/100000000000000 : ℝ)^3387
        have hw : |(-1875606063/10000000000 : ℝ)|=(1875606063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2703243019/5000000000 : ℝ)|^4411 ≤ (44891761811159/100000000000000 : ℝ)^3387
        have hw : |(2703243019/5000000000 : ℝ)|=(2703243019/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1451_s7_5 (p : ℝ) (hpa : (2205/512 : ℝ) ≤ p) (hpb : p ≤ (4411/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305252343/10000000000 : ℝ)*x 0 + (5406486123/10000000000 : ℝ)*x 1 + (-937802701/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305252343/10000000000 : ℝ)^4411 ≤ (43800165436219/100000000000000 : ℝ)^3387 := by
    have hnat : (5305252343 : ℕ)^4411*100000000000000^3387 ≤ 43800165436219^3387*10000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305252343 10000000000 43800165436219 100000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5406486123/10000000000 : ℝ)^4411 ≤ (22445881365161/50000000000000 : ℝ)^3387 := by
    have hnat : (5406486123 : ℕ)^4411*50000000000000^3387 ≤ 22445881365161^3387*10000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406486123 10000000000 22445881365161 50000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (937802701/5000000000 : ℝ)^4411 ≤ (353377244231/3125000000000 : ℝ)^3387 := by
    have hnat : (937802701 : ℕ)^4411*3125000000000^3387 ≤ 353377244231^3387*5000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      937802701 5000000000 353377244231 3125000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4411/1024 : ℝ)) 4411 3387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305252343/10000000000 : ℝ), (5406486123/10000000000 : ℝ), (-937802701/5000000000 : ℝ)] ![(43800165436219/100000000000000 : ℝ), (22445881365161/50000000000000 : ℝ), (353377244231/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305252343/10000000000 : ℝ)|^4411 ≤ (43800165436219/100000000000000 : ℝ)^3387
        have hw : |(5305252343/10000000000 : ℝ)|=(5305252343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5406486123/10000000000 : ℝ)|^4411 ≤ (22445881365161/50000000000000 : ℝ)^3387
        have hw : |(5406486123/10000000000 : ℝ)|=(5406486123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-937802701/5000000000 : ℝ)|^4411 ≤ (353377244231/3125000000000 : ℝ)^3387
        have hw : |(-937802701/5000000000 : ℝ)|=(937802701/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1451_s7_6 (p : ℝ) (hpa : (2205/512 : ℝ) ≤ p) (hpb : p ≤ (4411/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4298927551/10000000000 : ℝ)*x 0 + (559361691/1250000000 : ℝ)*x 1 + (4129203941/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4298927551/10000000000 : ℝ)^4411 ≤ (33305272828121/100000000000000 : ℝ)^3387 := by
    have hnat : (4298927551 : ℕ)^4411*100000000000000^3387 ≤ 33305272828121^3387*10000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4298927551 10000000000 33305272828121 100000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (559361691/1250000000 : ℝ)^4411 ≤ (7018317044913/20000000000000 : ℝ)^3387 := by
    have hnat : (559361691 : ℕ)^4411*20000000000000^3387 ≤ 7018317044913^3387*1250000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      559361691 1250000000 7018317044913 20000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4129203941/10000000000 : ℝ)^4411 ≤ (31603141922527/100000000000000 : ℝ)^3387 := by
    have hnat : (4129203941 : ℕ)^4411*100000000000000^3387 ≤ 31603141922527^3387*10000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4129203941 10000000000 31603141922527 100000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4411/1024 : ℝ)) 4411 3387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4298927551/10000000000 : ℝ), (559361691/1250000000 : ℝ), (4129203941/10000000000 : ℝ)] ![(33305272828121/100000000000000 : ℝ), (7018317044913/20000000000000 : ℝ), (31603141922527/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4298927551/10000000000 : ℝ)|^4411 ≤ (33305272828121/100000000000000 : ℝ)^3387
        have hw : |(4298927551/10000000000 : ℝ)|=(4298927551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(559361691/1250000000 : ℝ)|^4411 ≤ (7018317044913/20000000000000 : ℝ)^3387
        have hw : |(559361691/1250000000 : ℝ)|=(559361691/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4129203941/10000000000 : ℝ)|^4411 ≤ (31603141922527/100000000000000 : ℝ)^3387
        have hw : |(4129203941/10000000000 : ℝ)|=(4129203941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1451_s7_7 (p : ℝ) (hpa : (2205/512 : ℝ) ≤ p) (hpb : p ≤ (4411/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-5149057/2000000000 : ℝ)*x 0 + (293551433/500000000 : ℝ)*x 1 + (5870958341/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5149057/2000000000 : ℝ)^4411 ≤ (42449013619/100000000000000 : ℝ)^3387 := by
    have hnat : (5149057 : ℕ)^4411*100000000000000^3387 ≤ 42449013619^3387*2000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5149057 2000000000 42449013619 100000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (293551433/500000000 : ℝ)^4411 ≤ (9995833056333/20000000000000 : ℝ)^3387 := by
    have hnat : (293551433 : ℕ)^4411*20000000000000^3387 ≤ 9995833056333^3387*500000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      293551433 500000000 9995833056333 20000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5870958341/10000000000 : ℝ)^4411 ≤ (49978385687537/100000000000000 : ℝ)^3387 := by
    have hnat : (5870958341 : ℕ)^4411*100000000000000^3387 ≤ 49978385687537^3387*10000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5870958341 10000000000 49978385687537 100000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4411/1024 : ℝ)) 4411 3387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-5149057/2000000000 : ℝ), (293551433/500000000 : ℝ), (5870958341/10000000000 : ℝ)] ![(42449013619/100000000000000 : ℝ), (9995833056333/20000000000000 : ℝ), (49978385687537/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-5149057/2000000000 : ℝ)|^4411 ≤ (42449013619/100000000000000 : ℝ)^3387
        have hw : |(-5149057/2000000000 : ℝ)|=(5149057/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(293551433/500000000 : ℝ)|^4411 ≤ (9995833056333/20000000000000 : ℝ)^3387
        have hw : |(293551433/500000000 : ℝ)|=(293551433/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5870958341/10000000000 : ℝ)|^4411 ≤ (49978385687537/100000000000000 : ℝ)^3387
        have hw : |(5870958341/10000000000 : ℝ)|=(5870958341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1451_s7_8 (p : ℝ) (hpa : (2205/512 : ℝ) ≤ p) (hpb : p ≤ (4411/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1431161807/10000000000 : ℝ)*x 0 + (172198293/312500000 : ℝ)*x 1 + (2755756567/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1431161807/10000000000 : ℝ)^4411 ≤ (993884826653/12500000000000 : ℝ)^3387 := by
    have hnat : (1431161807 : ℕ)^4411*12500000000000^3387 ≤ 993884826653^3387*10000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1431161807 10000000000 993884826653 12500000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (172198293/312500000 : ℝ)^4411 ≤ (2876131886073/6250000000000 : ℝ)^3387 := by
    have hnat : (172198293 : ℕ)^4411*6250000000000^3387 ≤ 2876131886073^3387*312500000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      172198293 312500000 2876131886073 6250000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2755756567/5000000000 : ℝ)^4411 ≤ (23015405598343/50000000000000 : ℝ)^3387 := by
    have hnat : (2755756567 : ℕ)^4411*50000000000000^3387 ≤ 23015405598343^3387*5000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2755756567 5000000000 23015405598343 50000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4411/1024 : ℝ)) 4411 3387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1431161807/10000000000 : ℝ), (172198293/312500000 : ℝ), (2755756567/5000000000 : ℝ)] ![(993884826653/12500000000000 : ℝ), (2876131886073/6250000000000 : ℝ), (23015405598343/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1431161807/10000000000 : ℝ)|^4411 ≤ (993884826653/12500000000000 : ℝ)^3387
        have hw : |(1431161807/10000000000 : ℝ)|=(1431161807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(172198293/312500000 : ℝ)|^4411 ≤ (2876131886073/6250000000000 : ℝ)^3387
        have hw : |(172198293/312500000 : ℝ)|=(172198293/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2755756567/5000000000 : ℝ)|^4411 ≤ (23015405598343/50000000000000 : ℝ)^3387
        have hw : |(2755756567/5000000000 : ℝ)|=(2755756567/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1451_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2205/512 : ℝ) ≤ p) (hpb : p ≤ (4411/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (159039209/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (923/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1423/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (2277/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (923/6250 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (923/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1423/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (923/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1423/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (923/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1423/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (923/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1423/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (923/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1423/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (923/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1423/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1423/12500 : ℝ) ^ (2205/512 : ℝ) ≤ (345033460547177/4000000000000000000 : ℝ) := by
    have hpowers : (1423/12500 : ℝ)^2205 ≤ (345033460547177/4000000000000000000 : ℝ)^512 := by
      have hnat : (1423 : ℕ)^2205*4000000000000000000^512 ≤ 345033460547177^512*12500^2205 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1423 12500 345033460547177 4000000000000000000 2205 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1423/12500 : ℝ)) (X := (345033460547177/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2205 512 (by norm_num) hpowers
    exact h
  have hpowhi : (923/6250 : ℝ) ^ (2205/512 : ℝ) ≤ (165366309376521/625000000000000000 : ℝ) := by
    have hpowers : (923/6250 : ℝ)^2205 ≤ (165366309376521/625000000000000000 : ℝ)^512 := by
      have hnat : (923 : ℕ)^2205*625000000000000000^512 ≤ 165366309376521^512*6250^2205 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        923 6250 165366309376521 625000000000000000 2205 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (923/6250 : ℝ)) (X := (165366309376521/625000000000000000 : ℝ)) (by norm_num) (by norm_num) 2205 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (2000345033460547177/2000000000000000000 : ℝ) ≤ (10000400556537703/10000000000000000 : ℝ) ^ (2205/512 : ℝ) := by
    have hpowers : (2000345033460547177/2000000000000000000 : ℝ)^512 ≤ (10000400556537703/10000000000000000 : ℝ)^2205 := by
      have hnat : (2000345033460547177 : ℕ)^512*10000000000000000^2205 ≤ 10000400556537703^2205*2000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2000345033460547177 2000000000000000000 10000400556537703 10000000000000000 512 2205 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000400556537703/10000000000000000 : ℝ)) (X := (2000345033460547177/2000000000000000000 : ℝ)) (by norm_num) 2205 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (20007016889202784557/20000000000000000000 : ℝ) ≤ (2000162909908427/2000000000000000 : ℝ) ^ (2205/512 : ℝ) := by
    have hpowers : (20007016889202784557/20000000000000000000 : ℝ)^512 ≤ (2000162909908427/2000000000000000 : ℝ)^2205 := by
      have hnat : (20007016889202784557 : ℕ)^512*2000000000000000^2205 ≤ 2000162909908427^2205*20000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20007016889202784557 20000000000000000000 2000162909908427 2000000000000000 512 2205 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000162909908427/2000000000000000 : ℝ)) (X := (20007016889202784557/20000000000000000000 : ℝ)) (by norm_num) 2205 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (312665366309376521/312500000000000000 : ℝ) ≤ (10001228542546567/10000000000000000 : ℝ) ^ (2205/512 : ℝ) := by
    have hpowers : (312665366309376521/312500000000000000 : ℝ)^512 ≤ (10001228542546567/10000000000000000 : ℝ)^2205 := by
      have hnat : (312665366309376521 : ℕ)^512*10000000000000000^2205 ≤ 10001228542546567^2205*312500000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        312665366309376521 312500000000000000 10001228542546567 10000000000000000 512 2205 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001228542546567/10000000000000000 : ℝ)) (X := (312665366309376521/312500000000000000 : ℝ)) (by norm_num) 2205 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(345033460547177/4000000000000000000 : ℝ) ≤ ((1409663737108278299/1410000000000000000 : ℝ)+2*(8624854259/7050000000000 : ℝ)*(1423/12500 : ℝ))^(2205/512 : ℝ) := by
    rw [show (1409663737108278299/1410000000000000000 : ℝ)+2*(8624854259/7050000000000 : ℝ)*(1423/12500 : ℝ)=(10000400556537703/10000000000000000 : ℝ) by norm_num, show 1+2*(345033460547177/4000000000000000000 : ℝ)=(2000345033460547177/2000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(165366309376521/625000000000000000 : ℝ)+(345033460547177/4000000000000000000 : ℝ) ≤ ((1409663737108278299/1410000000000000000 : ℝ)+(8624854259/7050000000000 : ℝ)*((923/6250 : ℝ)+(1423/12500 : ℝ)))^(2205/512 : ℝ) := by
    rw [show (1409663737108278299/1410000000000000000 : ℝ)+(8624854259/7050000000000 : ℝ)*((923/6250 : ℝ)+(1423/12500 : ℝ))=(2000162909908427/2000000000000000 : ℝ) by norm_num, show 1+(165366309376521/625000000000000000 : ℝ)+(345033460547177/4000000000000000000 : ℝ)=(20007016889202784557/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(165366309376521/625000000000000000 : ℝ) ≤ ((1409663737108278299/1410000000000000000 : ℝ)+2*(8624854259/7050000000000 : ℝ)*(923/6250 : ℝ))^(2205/512 : ℝ) := by
    rw [show (1409663737108278299/1410000000000000000 : ℝ)+2*(8624854259/7050000000000 : ℝ)*(923/6250 : ℝ)=(10001228542546567/10000000000000000 : ℝ) by norm_num, show 1+2*(165366309376521/625000000000000000 : ℝ)=(312665366309376521/312500000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1409663737108278299/1410000000000000000 : ℝ)*(X 1 0+X 2 0)+(8624854259/7050000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2205/512 : ℝ)) (lo := (1423/12500 : ℝ)) (hi := (923/6250 : ℝ)) (c := (1409663737108278299/1410000000000000000 : ℝ)) (alpha := (8624854259/7050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1409663737108278299/1410000000000000000 : ℝ)*(X 0 1+X 2 1)+(8624854259/7050000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2205/512 : ℝ)) (lo := (1423/12500 : ℝ)) (hi := (923/6250 : ℝ)) (c := (1409663737108278299/1410000000000000000 : ℝ)) (alpha := (8624854259/7050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1409663737108278299/1410000000000000000 : ℝ)*(X 0 2+X 1 2)+(8624854259/7050000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2205/512 : ℝ)) (lo := (1423/12500 : ℝ)) (hi := (923/6250 : ℝ)) (c := (1409663737108278299/1410000000000000000 : ℝ)) (alpha := (8624854259/7050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1953423733/10000000000 : ℝ)*X 0 0+(540706421/1000000000 : ℝ)*X 0 1+(5247394677/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1451_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1069370371/2000000000 : ℝ)*X 1 0+(-2034699197/10000000000 : ℝ)*X 1 1+(2623695681/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1451_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5346850779/10000000000 : ℝ)*X 2 0+(262369659/500000000 : ℝ)*X 2 1+(-254337277/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1451_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2149451071/5000000000 : ℝ)*X 0 0+(4127941441/10000000000 : ℝ)*X 0 1+(279759419/625000000 : ℝ)*X 0 2+(2149451071/5000000000 : ℝ)*X 1 0+(4127941441/10000000000 : ℝ)*X 1 1+(279759419/625000000 : ℝ)*X 1 2+(2149451071/5000000000 : ℝ)*X 2 0+(4127941441/10000000000 : ℝ)*X 2 1+(279759419/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1451_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((2652625973/5000000000 : ℝ)*X 1 0+(-1875606063/10000000000 : ℝ)*X 1 1+(2703243019/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1451_s7_4 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305252343/10000000000 : ℝ)*X 2 0+(5406486123/10000000000 : ℝ)*X 2 1+(-937802701/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1451_s7_5 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((4298927551/10000000000 : ℝ)*X 0 0+(559361691/1250000000 : ℝ)*X 0 1+(4129203941/10000000000 : ℝ)*X 0 2+(4298927551/10000000000 : ℝ)*X 1 0+(559361691/1250000000 : ℝ)*X 1 1+(4129203941/10000000000 : ℝ)*X 1 2+(4298927551/10000000000 : ℝ)*X 2 0+(559361691/1250000000 : ℝ)*X 2 1+(4129203941/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1451_s7_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((-5149057/2000000000 : ℝ)*X 0 0+(293551433/500000000 : ℝ)*X 0 1+(5870958341/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1451_s7_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((1431161807/10000000000 : ℝ)*X 0 0+(172198293/312500000 : ℝ)*X 0 1+(2755756567/5000000000 : ℝ)*X 0 2+(1431161807/10000000000 : ℝ)*X 1 0+(172198293/312500000 : ℝ)*X 1 1+(2755756567/5000000000 : ℝ)*X 1 2+(1431161807/10000000000 : ℝ)*X 2 0+(172198293/312500000 : ℝ)*X 2 1+(2755756567/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1451_s7_8 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7498059175008765480411867/11750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (670532007/50000000000000 : ℝ)*(lower3) + (304565461/50000000000000 : ℝ)*(lower4) + (2283696982177967/50000000000000 : ℝ)*(major0) + (2283696982177967/50000000000000 : ℝ)*(major1) + (2283696982177967/50000000000000 : ℝ)*(major2) + (6262907389145469/100000000000000 : ℝ)*(sp0) + (3131410312147459/50000000000000 : ℝ)*(sp1) + (3131418094240793/50000000000000 : ℝ)*(sp2) + (2871865148085659/100000000000000 : ℝ)*(sp3) + (100657881179/100000000000000 : ℝ)*(sp4) + (85093694511/100000000000000 : ℝ)*(sp5) + (88070343/10000000000000 : ℝ)*(sp6) + (13893030627/100000000000000 : ℝ)*(sp7) + (596475587/100000000000000 : ℝ)*(sp8) + (717966656316169/25000000000000 : ℝ)*(f.failure) + (6262921282176097/100000000000000 : ℝ)*(f.sum) + (229576914413/705000000000000000000000000 : ℝ)*base66 + (145255548120712711/23500000000000000000000000000000 : ℝ)*base67 + (25973217340212711/23500000000000000000000000000000 : ℝ)*base69 + (181929207260712711/23500000000000000000000000000000 : ℝ)*base71 + (509411059757/176250000000000000000000000 : ℝ)*base74 + (115421554412787289/23500000000000000000000000000000 : ℝ)*base76 + (110371959999787289/23500000000000000000000000000000 : ℝ)*base78 + (47344677580212711/23500000000000000000000000000000 : ℝ)*base79 + (1016344036759/352500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (21670321/2500000000000000000000 : ℝ)*base89 + (21670321/2500000000000000000000 : ℝ)*base91 + (21670321/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(upper0) + hcertificate_margin
theorem rectangle_w1451_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2205/512 : ℝ) ≤ p) (hpb : p ≤ (4411/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (159039209/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (923/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1423/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2277/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (923/6250 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1451_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1451_box_0 (p : ℝ) (hpa : (2205/512 : ℝ) ≤ p) (hpb : p ≤ (4411/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-358865829/2000000000 : ℝ)*x 0 + (1346328113/2500000000 : ℝ)*x 1 + (5385312741/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (358865829/2000000000 : ℝ)^4411 ≤ (2134826112007/20000000000000 : ℝ)^3387 := by
    have hnat : (358865829 : ℕ)^4411*20000000000000^3387 ≤ 2134826112007^3387*2000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      358865829 2000000000 2134826112007 20000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1346328113/2500000000 : ℝ)^4411 ≤ (22331466574367/50000000000000 : ℝ)^3387 := by
    have hnat : (1346328113 : ℕ)^4411*50000000000000^3387 ≤ 22331466574367^3387*2500000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1346328113 2500000000 22331466574367 50000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5385312741/10000000000 : ℝ)^4411 ≤ (22331468135091/50000000000000 : ℝ)^3387 := by
    have hnat : (5385312741 : ℕ)^4411*50000000000000^3387 ≤ 22331468135091^3387*10000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5385312741 10000000000 22331468135091 50000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4411/1024 : ℝ)) 4411 3387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-358865829/2000000000 : ℝ), (1346328113/2500000000 : ℝ), (5385312741/10000000000 : ℝ)] ![(2134826112007/20000000000000 : ℝ), (22331466574367/50000000000000 : ℝ), (22331468135091/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-358865829/2000000000 : ℝ)|^4411 ≤ (2134826112007/20000000000000 : ℝ)^3387
        have hw : |(-358865829/2000000000 : ℝ)|=(358865829/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1346328113/2500000000 : ℝ)|^4411 ≤ (22331466574367/50000000000000 : ℝ)^3387
        have hw : |(1346328113/2500000000 : ℝ)|=(1346328113/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5385312741/10000000000 : ℝ)|^4411 ≤ (22331468135091/50000000000000 : ℝ)^3387
        have hw : |(5385312741/10000000000 : ℝ)|=(5385312741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1451_box_1 (p : ℝ) (hpa : (2205/512 : ℝ) ≤ p) (hpb : p ≤ (4411/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2643102199/5000000000 : ℝ)*x 0 + (-386115181/2000000000 : ℝ)*x 1 + (107706261/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2643102199/5000000000 : ℝ)^4411 ≤ (43595472091901/100000000000000 : ℝ)^3387 := by
    have hnat : (2643102199 : ℕ)^4411*100000000000000^3387 ≤ 43595472091901^3387*5000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2643102199 5000000000 43595472091901 100000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (386115181/2000000000 : ℝ)^4411 ≤ (11741588290957/100000000000000 : ℝ)^3387 := by
    have hnat : (386115181 : ℕ)^4411*100000000000000^3387 ≤ 11741588290957^3387*2000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      386115181 2000000000 11741588290957 100000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (107706261/200000000 : ℝ)^4411 ≤ (22331469803823/50000000000000 : ℝ)^3387 := by
    have hnat : (107706261 : ℕ)^4411*50000000000000^3387 ≤ 22331469803823^3387*200000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107706261 200000000 22331469803823 50000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4411/1024 : ℝ)) 4411 3387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2643102199/5000000000 : ℝ), (-386115181/2000000000 : ℝ), (107706261/200000000 : ℝ)] ![(43595472091901/100000000000000 : ℝ), (11741588290957/100000000000000 : ℝ), (22331469803823/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2643102199/5000000000 : ℝ)|^4411 ≤ (43595472091901/100000000000000 : ℝ)^3387
        have hw : |(2643102199/5000000000 : ℝ)|=(2643102199/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-386115181/2000000000 : ℝ)|^4411 ≤ (11741588290957/100000000000000 : ℝ)^3387
        have hw : |(-386115181/2000000000 : ℝ)|=(386115181/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(107706261/200000000 : ℝ)|^4411 ≤ (22331469803823/50000000000000 : ℝ)^3387
        have hw : |(107706261/200000000 : ℝ)|=(107706261/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1451_box_2 (p : ℝ) (hpa : (2205/512 : ℝ) ≤ p) (hpb : p ≤ (4411/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2643102501/5000000000 : ℝ)*x 0 + (538531261/1000000000 : ℝ)*x 1 + (-386115137/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2643102501/5000000000 : ℝ)^4411 ≤ (8719095715817/20000000000000 : ℝ)^3387 := by
    have hnat : (2643102501 : ℕ)^4411*20000000000000^3387 ≤ 8719095715817^3387*5000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2643102501 5000000000 8719095715817 20000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (538531261/1000000000 : ℝ)^4411 ≤ (44662934855269/100000000000000 : ℝ)^3387 := by
    have hnat : (538531261 : ℕ)^4411*100000000000000^3387 ≤ 44662934855269^3387*1000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      538531261 1000000000 44662934855269 100000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (386115137/2000000000 : ℝ)^4411 ≤ (1174158654841/10000000000000 : ℝ)^3387 := by
    have hnat : (386115137 : ℕ)^4411*10000000000000^3387 ≤ 1174158654841^3387*2000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      386115137 2000000000 1174158654841 10000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4411/1024 : ℝ)) 4411 3387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2643102501/5000000000 : ℝ), (538531261/1000000000 : ℝ), (-386115137/2000000000 : ℝ)] ![(8719095715817/20000000000000 : ℝ), (44662934855269/100000000000000 : ℝ), (1174158654841/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2643102501/5000000000 : ℝ)|^4411 ≤ (8719095715817/20000000000000 : ℝ)^3387
        have hw : |(2643102501/5000000000 : ℝ)|=(2643102501/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(538531261/1000000000 : ℝ)|^4411 ≤ (44662934855269/100000000000000 : ℝ)^3387
        have hw : |(538531261/1000000000 : ℝ)|=(538531261/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-386115137/2000000000 : ℝ)|^4411 ≤ (1174158654841/10000000000000 : ℝ)^3387
        have hw : |(-386115137/2000000000 : ℝ)|=(386115137/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1451_box_3 (p : ℝ) (hpa : (2205/512 : ℝ) ≤ p) (hpb : p ≤ (4411/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4444770989/10000000000 : ℝ)*x 0 + (4229636819/10000000000 : ℝ)*x 1 + (422963717/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4444770989/10000000000 : ℝ)^4411 ≤ (8696066297469/25000000000000 : ℝ)^3387 := by
    have hnat : (4444770989 : ℕ)^4411*25000000000000^3387 ≤ 8696066297469^3387*10000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4444770989 10000000000 8696066297469 25000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4229636819/10000000000 : ℝ)^4411 ≤ (3260786564127/10000000000000 : ℝ)^3387 := by
    have hnat : (4229636819 : ℕ)^4411*10000000000000^3387 ≤ 3260786564127^3387*10000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4229636819 10000000000 3260786564127 10000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (422963717/1000000000 : ℝ)^4411 ≤ (3260786916537/10000000000000 : ℝ)^3387 := by
    have hnat : (422963717 : ℕ)^4411*10000000000000^3387 ≤ 3260786916537^3387*1000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      422963717 1000000000 3260786916537 10000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4411/1024 : ℝ)) 4411 3387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4444770989/10000000000 : ℝ), (4229636819/10000000000 : ℝ), (422963717/1000000000 : ℝ)] ![(8696066297469/25000000000000 : ℝ), (3260786564127/10000000000000 : ℝ), (3260786916537/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4444770989/10000000000 : ℝ)|^4411 ≤ (8696066297469/25000000000000 : ℝ)^3387
        have hw : |(4444770989/10000000000 : ℝ)|=(4444770989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4229636819/10000000000 : ℝ)|^4411 ≤ (3260786564127/10000000000000 : ℝ)^3387
        have hw : |(4229636819/10000000000 : ℝ)|=(4229636819/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(422963717/1000000000 : ℝ)|^4411 ≤ (3260786916537/10000000000000 : ℝ)^3387
        have hw : |(422963717/1000000000 : ℝ)|=(422963717/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1451_box_4 (p : ℝ) (hpa : (2205/512 : ℝ) ≤ p) (hpb : p ≤ (4411/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-132202523/625000000 : ℝ)*x 0 + (5266832349/10000000000 : ℝ)*x 1 + (5266832331/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (132202523/625000000 : ℝ)^4411 ≤ (1322495128223/10000000000000 : ℝ)^3387 := by
    have hnat : (132202523 : ℕ)^4411*10000000000000^3387 ≤ 1322495128223^3387*625000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132202523 625000000 1322495128223 10000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266832349/10000000000 : ℝ)^4411 ≤ (21693762226173/50000000000000 : ℝ)^3387 := by
    have hnat : (5266832349 : ℕ)^4411*50000000000000^3387 ≤ 21693762226173^3387*10000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266832349 10000000000 21693762226173 50000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266832331/10000000000 : ℝ)^4411 ≤ (21693762129617/50000000000000 : ℝ)^3387 := by
    have hnat : (5266832331 : ℕ)^4411*50000000000000^3387 ≤ 21693762129617^3387*10000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266832331 10000000000 21693762129617 50000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4411/1024 : ℝ)) 4411 3387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-132202523/625000000 : ℝ), (5266832349/10000000000 : ℝ), (5266832331/10000000000 : ℝ)] ![(1322495128223/10000000000000 : ℝ), (21693762226173/50000000000000 : ℝ), (21693762129617/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-132202523/625000000 : ℝ)|^4411 ≤ (1322495128223/10000000000000 : ℝ)^3387
        have hw : |(-132202523/625000000 : ℝ)|=(132202523/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266832349/10000000000 : ℝ)|^4411 ≤ (21693762226173/50000000000000 : ℝ)^3387
        have hw : |(5266832349/10000000000 : ℝ)|=(5266832349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266832331/10000000000 : ℝ)|^4411 ≤ (21693762129617/50000000000000 : ℝ)^3387
        have hw : |(5266832331/10000000000 : ℝ)|=(5266832331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1451_box_5 (p : ℝ) (hpa : (2205/512 : ℝ) ≤ p) (hpb : p ≤ (4411/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5369049301/10000000000 : ℝ)*x 0 + (-989408089/5000000000 : ℝ)*x 1 + (2633416157/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5369049301/10000000000 : ℝ)^4411 ≤ (22243678716593/50000000000000 : ℝ)^3387 := by
    have hnat : (5369049301 : ℕ)^4411*50000000000000^3387 ≤ 22243678716593^3387*10000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5369049301 10000000000 22243678716593 50000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (989408089/5000000000 : ℝ)^4411 ≤ (3031279617399/25000000000000 : ℝ)^3387 := by
    have hnat : (989408089 : ℕ)^4411*25000000000000^3387 ≤ 3031279617399^3387*5000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      989408089 5000000000 3031279617399 25000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2633416157/5000000000 : ℝ)^4411 ≤ (867750481537/2000000000000 : ℝ)^3387 := by
    have hnat : (2633416157 : ℕ)^4411*2000000000000^3387 ≤ 867750481537^3387*5000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633416157 5000000000 867750481537 2000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4411/1024 : ℝ)) 4411 3387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5369049301/10000000000 : ℝ), (-989408089/5000000000 : ℝ), (2633416157/5000000000 : ℝ)] ![(22243678716593/50000000000000 : ℝ), (3031279617399/25000000000000 : ℝ), (867750481537/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5369049301/10000000000 : ℝ)|^4411 ≤ (22243678716593/50000000000000 : ℝ)^3387
        have hw : |(5369049301/10000000000 : ℝ)|=(5369049301/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-989408089/5000000000 : ℝ)|^4411 ≤ (3031279617399/25000000000000 : ℝ)^3387
        have hw : |(-989408089/5000000000 : ℝ)|=(989408089/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2633416157/5000000000 : ℝ)|^4411 ≤ (867750481537/2000000000000 : ℝ)^3387
        have hw : |(2633416157/5000000000 : ℝ)|=(2633416157/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1451_box_6 (p : ℝ) (hpa : (2205/512 : ℝ) ≤ p) (hpb : p ≤ (4411/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5369049459/10000000000 : ℝ)*x 0 + (5266832251/10000000000 : ℝ)*x 1 + (-39576321/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5369049459/10000000000 : ℝ)^4411 ≤ (44487359138161/100000000000000 : ℝ)^3387 := by
    have hnat : (5369049459 : ℕ)^4411*100000000000000^3387 ≤ 44487359138161^3387*10000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5369049459 10000000000 44487359138161 100000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266832251/10000000000 : ℝ)^4411 ≤ (43387523400957/100000000000000 : ℝ)^3387 := by
    have hnat : (5266832251 : ℕ)^4411*100000000000000^3387 ≤ 43387523400957^3387*10000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266832251 10000000000 43387523400957 100000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (39576321/200000000 : ℝ)^4411 ≤ (12125117448157/100000000000000 : ℝ)^3387 := by
    have hnat : (39576321 : ℕ)^4411*100000000000000^3387 ≤ 12125117448157^3387*200000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      39576321 200000000 12125117448157 100000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4411/1024 : ℝ)) 4411 3387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5369049459/10000000000 : ℝ), (5266832251/10000000000 : ℝ), (-39576321/200000000 : ℝ)] ![(44487359138161/100000000000000 : ℝ), (43387523400957/100000000000000 : ℝ), (12125117448157/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5369049459/10000000000 : ℝ)|^4411 ≤ (44487359138161/100000000000000 : ℝ)^3387
        have hw : |(5369049459/10000000000 : ℝ)|=(5369049459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266832251/10000000000 : ℝ)|^4411 ≤ (43387523400957/100000000000000 : ℝ)^3387
        have hw : |(5266832251/10000000000 : ℝ)|=(5266832251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-39576321/200000000 : ℝ)|^4411 ≤ (12125117448157/100000000000000 : ℝ)^3387
        have hw : |(-39576321/200000000 : ℝ)|=(39576321/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1451_box_7 (p : ℝ) (hpa : (2205/512 : ℝ) ≤ p) (hpb : p ≤ (4411/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4151958859/10000000000 : ℝ)*x 0 + (4375992659/10000000000 : ℝ)*x 1 + (2187996453/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4151958859/10000000000 : ℝ)^4411 ≤ (1273205601157/4000000000000 : ℝ)^3387 := by
    have hnat : (4151958859 : ℕ)^4411*4000000000000^3387 ≤ 1273205601157^3387*10000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4151958859 10000000000 1273205601157 4000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4375992659/10000000000 : ℝ)^4411 ≤ (6816985744413/20000000000000 : ℝ)^3387 := by
    have hnat : (4375992659 : ℕ)^4411*20000000000000^3387 ≤ 6816985744413^3387*10000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4375992659 10000000000 6816985744413 20000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2187996453/5000000000 : ℝ)^4411 ≤ (4260616403453/12500000000000 : ℝ)^3387 := by
    have hnat : (2187996453 : ℕ)^4411*12500000000000^3387 ≤ 4260616403453^3387*5000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2187996453 5000000000 4260616403453 12500000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4411/1024 : ℝ)) 4411 3387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4151958859/10000000000 : ℝ), (4375992659/10000000000 : ℝ), (2187996453/5000000000 : ℝ)] ![(1273205601157/4000000000000 : ℝ), (6816985744413/20000000000000 : ℝ), (4260616403453/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4151958859/10000000000 : ℝ)|^4411 ≤ (1273205601157/4000000000000 : ℝ)^3387
        have hw : |(4151958859/10000000000 : ℝ)|=(4151958859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4375992659/10000000000 : ℝ)|^4411 ≤ (6816985744413/20000000000000 : ℝ)^3387
        have hw : |(4375992659/10000000000 : ℝ)|=(4375992659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2187996453/5000000000 : ℝ)|^4411 ≤ (4260616403453/12500000000000 : ℝ)^3387
        have hw : |(2187996453/5000000000 : ℝ)|=(2187996453/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1451_box_8 (p : ℝ) (hpa : (2205/512 : ℝ) ≤ p) (hpb : p ≤ (4411/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-51190011/250000000 : ℝ)*x 0 + (324048951/625000000 : ℝ)*x 1 + (5399272997/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (51190011/250000000 : ℝ)^4411 ≤ (6338438755441/50000000000000 : ℝ)^3387 := by
    have hnat : (51190011 : ℕ)^4411*50000000000000^3387 ≤ 6338438755441^3387*250000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      51190011 250000000 6338438755441 50000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (324048951/625000000 : ℝ)^4411 ≤ (42509344429191/100000000000000 : ℝ)^3387 := by
    have hnat : (324048951 : ℕ)^4411*100000000000000^3387 ≤ 42509344429191^3387*625000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      324048951 625000000 42509344429191 100000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5399272997/10000000000 : ℝ)^4411 ≤ (4481377804549/10000000000000 : ℝ)^3387 := by
    have hnat : (5399272997 : ℕ)^4411*10000000000000^3387 ≤ 4481377804549^3387*10000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5399272997 10000000000 4481377804549 10000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4411/1024 : ℝ)) 4411 3387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-51190011/250000000 : ℝ), (324048951/625000000 : ℝ), (5399272997/10000000000 : ℝ)] ![(6338438755441/50000000000000 : ℝ), (42509344429191/100000000000000 : ℝ), (4481377804549/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-51190011/250000000 : ℝ)|^4411 ≤ (6338438755441/50000000000000 : ℝ)^3387
        have hw : |(-51190011/250000000 : ℝ)|=(51190011/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(324048951/625000000 : ℝ)|^4411 ≤ (42509344429191/100000000000000 : ℝ)^3387
        have hw : |(324048951/625000000 : ℝ)|=(324048951/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5399272997/10000000000 : ℝ)|^4411 ≤ (4481377804549/10000000000000 : ℝ)^3387
        have hw : |(5399272997/10000000000 : ℝ)|=(5399272997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1451_box_9 (p : ℝ) (hpa : (2205/512 : ℝ) ≤ p) (hpb : p ≤ (4411/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1319109943/2500000000 : ℝ)*x 0 + (-192476703/1000000000 : ℝ)*x 1 + (2699636369/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1319109943/2500000000 : ℝ)^4411 ≤ (43490625680621/100000000000000 : ℝ)^3387 := by
    have hnat : (1319109943 : ℕ)^4411*100000000000000^3387 ≤ 43490625680621^3387*2500000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1319109943 2500000000 43490625680621 100000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (192476703/1000000000 : ℝ)^4411 ≤ (11695599060737/100000000000000 : ℝ)^3387 := by
    have hnat : (192476703 : ℕ)^4411*100000000000000^3387 ≤ 11695599060737^3387*1000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      192476703 1000000000 11695599060737 100000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2699636369/5000000000 : ℝ)^4411 ≤ (44813775245877/100000000000000 : ℝ)^3387 := by
    have hnat : (2699636369 : ℕ)^4411*100000000000000^3387 ≤ 44813775245877^3387*5000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2699636369 5000000000 44813775245877 100000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4411/1024 : ℝ)) 4411 3387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1319109943/2500000000 : ℝ), (-192476703/1000000000 : ℝ), (2699636369/5000000000 : ℝ)] ![(43490625680621/100000000000000 : ℝ), (11695599060737/100000000000000 : ℝ), (44813775245877/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1319109943/2500000000 : ℝ)|^4411 ≤ (43490625680621/100000000000000 : ℝ)^3387
        have hw : |(1319109943/2500000000 : ℝ)|=(1319109943/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-192476703/1000000000 : ℝ)|^4411 ≤ (11695599060737/100000000000000 : ℝ)^3387
        have hw : |(-192476703/1000000000 : ℝ)|=(192476703/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2699636369/5000000000 : ℝ)|^4411 ≤ (44813775245877/100000000000000 : ℝ)^3387
        have hw : |(2699636369/5000000000 : ℝ)|=(2699636369/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1451_box_10 (p : ℝ) (hpa : (2205/512 : ℝ) ≤ p) (hpb : p ≤ (4411/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5276439971/10000000000 : ℝ)*x 0 + (2699636237/5000000000 : ℝ)*x 1 + (-24059589/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5276439971/10000000000 : ℝ)^4411 ≤ (1087265695419/2500000000000 : ℝ)^3387 := by
    have hnat : (5276439971 : ℕ)^4411*2500000000000^3387 ≤ 1087265695419^3387*10000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5276439971 10000000000 1087265695419 2500000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2699636237/5000000000 : ℝ)^4411 ≤ (44813772392219/100000000000000 : ℝ)^3387 := by
    have hnat : (2699636237 : ℕ)^4411*100000000000000^3387 ≤ 44813772392219^3387*5000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2699636237 5000000000 44813772392219 100000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (24059589/125000000 : ℝ)^4411 ≤ (2923899943237/25000000000000 : ℝ)^3387 := by
    have hnat : (24059589 : ℕ)^4411*25000000000000^3387 ≤ 2923899943237^3387*125000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      24059589 125000000 2923899943237 25000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4411/1024 : ℝ)) 4411 3387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5276439971/10000000000 : ℝ), (2699636237/5000000000 : ℝ), (-24059589/125000000 : ℝ)] ![(1087265695419/2500000000000 : ℝ), (44813772392219/100000000000000 : ℝ), (2923899943237/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5276439971/10000000000 : ℝ)|^4411 ≤ (1087265695419/2500000000000 : ℝ)^3387
        have hw : |(5276439971/10000000000 : ℝ)|=(5276439971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2699636237/5000000000 : ℝ)|^4411 ≤ (44813772392219/100000000000000 : ℝ)^3387
        have hw : |(2699636237/5000000000 : ℝ)|=(2699636237/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-24059589/125000000 : ℝ)|^4411 ≤ (2923899943237/25000000000000 : ℝ)^3387
        have hw : |(-24059589/125000000 : ℝ)|=(24059589/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1451_box_11 (p : ℝ) (hpa : (2205/512 : ℝ) ≤ p) (hpb : p ≤ (4411/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (447871613/1000000000 : ℝ)*x 0 + (4212377281/10000000000 : ℝ)*x 1 + (1053094387/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (447871613/1000000000 : ℝ)^4411 ≤ (3513062949309/10000000000000 : ℝ)^3387 := by
    have hnat : (447871613 : ℕ)^4411*10000000000000^3387 ≤ 3513062949309^3387*1000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      447871613 1000000000 3513062949309 10000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4212377281/10000000000 : ℝ)^4411 ≤ (1297387356197/4000000000000 : ℝ)^3387 := by
    have hnat : (4212377281 : ℕ)^4411*4000000000000^3387 ≤ 1297387356197^3387*10000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4212377281 10000000000 1297387356197 4000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1053094387/2500000000 : ℝ)^4411 ≤ (32434686582339/100000000000000 : ℝ)^3387 := by
    have hnat : (1053094387 : ℕ)^4411*100000000000000^3387 ≤ 32434686582339^3387*2500000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053094387 2500000000 32434686582339 100000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4411/1024 : ℝ)) 4411 3387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(447871613/1000000000 : ℝ), (4212377281/10000000000 : ℝ), (1053094387/2500000000 : ℝ)] ![(3513062949309/10000000000000 : ℝ), (1297387356197/4000000000000 : ℝ), (32434686582339/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(447871613/1000000000 : ℝ)|^4411 ≤ (3513062949309/10000000000000 : ℝ)^3387
        have hw : |(447871613/1000000000 : ℝ)|=(447871613/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4212377281/10000000000 : ℝ)|^4411 ≤ (1297387356197/4000000000000 : ℝ)^3387
        have hw : |(4212377281/10000000000 : ℝ)|=(4212377281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1053094387/2500000000 : ℝ)|^4411 ≤ (32434686582339/100000000000000 : ℝ)^3387
        have hw : |(1053094387/2500000000 : ℝ)|=(1053094387/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1451_box_12 (p : ℝ) (hpa : (2205/512 : ℝ) ≤ p) (hpb : p ≤ (4411/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1862113201/10000000000 : ℝ)*x 0 + (1366344917/2500000000 : ℝ)*x 1 + (5255695939/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1862113201/10000000000 : ℝ)^4411 ≤ (11202249213077/100000000000000 : ℝ)^3387 := by
    have hnat : (1862113201 : ℕ)^4411*100000000000000^3387 ≤ 11202249213077^3387*10000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1862113201 10000000000 11202249213077 100000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1366344917/2500000000 : ℝ)^4411 ≤ (22764832301139/50000000000000 : ℝ)^3387 := by
    have hnat : (1366344917 : ℕ)^4411*50000000000000^3387 ≤ 22764832301139^3387*2500000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1366344917 2500000000 22764832301139 50000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5255695939/10000000000 : ℝ)^4411 ≤ (21634043085591/50000000000000 : ℝ)^3387 := by
    have hnat : (5255695939 : ℕ)^4411*50000000000000^3387 ≤ 21634043085591^3387*10000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5255695939 10000000000 21634043085591 50000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4411/1024 : ℝ)) 4411 3387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1862113201/10000000000 : ℝ), (1366344917/2500000000 : ℝ), (5255695939/10000000000 : ℝ)] ![(11202249213077/100000000000000 : ℝ), (22764832301139/50000000000000 : ℝ), (21634043085591/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1862113201/10000000000 : ℝ)|^4411 ≤ (11202249213077/100000000000000 : ℝ)^3387
        have hw : |(-1862113201/10000000000 : ℝ)|=(1862113201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1366344917/2500000000 : ℝ)|^4411 ≤ (22764832301139/50000000000000 : ℝ)^3387
        have hw : |(1366344917/2500000000 : ℝ)|=(1366344917/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5255695939/10000000000 : ℝ)|^4411 ≤ (21634043085591/50000000000000 : ℝ)^3387
        have hw : |(5255695939/10000000000 : ℝ)|=(5255695939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1451_box_13 (p : ℝ) (hpa : (2205/512 : ℝ) ≤ p) (hpb : p ≤ (4411/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5376834663/10000000000 : ℝ)*x 0 + (-991625787/5000000000 : ℝ)*x 1 + (1313924017/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5376834663/10000000000 : ℝ)^4411 ≤ (44571387564727/100000000000000 : ℝ)^3387 := by
    have hnat : (5376834663 : ℕ)^4411*100000000000000^3387 ≤ 44571387564727^3387*10000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5376834663 10000000000 44571387564727 100000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (991625787/5000000000 : ℝ)^4411 ≤ (12160524876027/100000000000000 : ℝ)^3387 := by
    have hnat : (991625787 : ℕ)^4411*100000000000000^3387 ≤ 12160524876027^3387*5000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      991625787 5000000000 12160524876027 100000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1313924017/2500000000 : ℝ)^4411 ≤ (10817021888567/25000000000000 : ℝ)^3387 := by
    have hnat : (1313924017 : ℕ)^4411*25000000000000^3387 ≤ 10817021888567^3387*2500000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1313924017 2500000000 10817021888567 25000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4411/1024 : ℝ)) 4411 3387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5376834663/10000000000 : ℝ), (-991625787/5000000000 : ℝ), (1313924017/2500000000 : ℝ)] ![(44571387564727/100000000000000 : ℝ), (12160524876027/100000000000000 : ℝ), (10817021888567/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5376834663/10000000000 : ℝ)|^4411 ≤ (44571387564727/100000000000000 : ℝ)^3387
        have hw : |(5376834663/10000000000 : ℝ)|=(5376834663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-991625787/5000000000 : ℝ)|^4411 ≤ (12160524876027/100000000000000 : ℝ)^3387
        have hw : |(-991625787/5000000000 : ℝ)|=(991625787/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1313924017/2500000000 : ℝ)|^4411 ≤ (10817021888567/25000000000000 : ℝ)^3387
        have hw : |(1313924017/2500000000 : ℝ)|=(1313924017/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1451_box_14 (p : ℝ) (hpa : (2205/512 : ℝ) ≤ p) (hpb : p ≤ (4411/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2688417271/5000000000 : ℝ)*x 0 + (5255696117/10000000000 : ℝ)*x 1 + (-1983251671/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2688417271/5000000000 : ℝ)^4411 ≤ (22285693129223/50000000000000 : ℝ)^3387 := by
    have hnat : (2688417271 : ℕ)^4411*50000000000000^3387 ≤ 22285693129223^3387*5000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2688417271 5000000000 22285693129223 50000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5255696117/10000000000 : ℝ)^4411 ≤ (21634044039813/50000000000000 : ℝ)^3387 := by
    have hnat : (5255696117 : ℕ)^4411*50000000000000^3387 ≤ 21634044039813^3387*10000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5255696117 10000000000 21634044039813 50000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1983251671/10000000000 : ℝ)^4411 ≤ (1216052565061/10000000000000 : ℝ)^3387 := by
    have hnat : (1983251671 : ℕ)^4411*10000000000000^3387 ≤ 1216052565061^3387*10000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1983251671 10000000000 1216052565061 10000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4411/1024 : ℝ)) 4411 3387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2688417271/5000000000 : ℝ), (5255696117/10000000000 : ℝ), (-1983251671/10000000000 : ℝ)] ![(22285693129223/50000000000000 : ℝ), (21634044039813/50000000000000 : ℝ), (1216052565061/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2688417271/5000000000 : ℝ)|^4411 ≤ (22285693129223/50000000000000 : ℝ)^3387
        have hw : |(2688417271/5000000000 : ℝ)|=(2688417271/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5255696117/10000000000 : ℝ)|^4411 ≤ (21634044039813/50000000000000 : ℝ)^3387
        have hw : |(5255696117/10000000000 : ℝ)|=(5255696117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1983251671/10000000000 : ℝ)|^4411 ≤ (1216052565061/10000000000000 : ℝ)^3387
        have hw : |(-1983251671/10000000000 : ℝ)|=(1983251671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1451_box_15 (p : ℝ) (hpa : (2205/512 : ℝ) ≤ p) (hpb : p ≤ (4411/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4123986383/10000000000 : ℝ)*x 0 + (137179317/312500000 : ℝ)*x 1 + (2194868921/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4123986383/10000000000 : ℝ)^4411 ≤ (7887786476051/25000000000000 : ℝ)^3387 := by
    have hnat : (4123986383 : ℕ)^4411*25000000000000^3387 ≤ 7887786476051^3387*10000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4123986383 10000000000 7887786476051 25000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (137179317/312500000 : ℝ)^4411 ≤ (34224428575567/100000000000000 : ℝ)^3387 := by
    have hnat : (137179317 : ℕ)^4411*100000000000000^3387 ≤ 34224428575567^3387*312500000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      137179317 312500000 34224428575567 100000000000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2194868921/5000000000 : ℝ)^4411 ≤ (534756648581/1562500000000 : ℝ)^3387 := by
    have hnat : (2194868921 : ℕ)^4411*1562500000000^3387 ≤ 534756648581^3387*5000000000^4411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2194868921 5000000000 534756648581 1562500000000 4411 3387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4411/1024 : ℝ)) 4411 3387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4123986383/10000000000 : ℝ), (137179317/312500000 : ℝ), (2194868921/5000000000 : ℝ)] ![(7887786476051/25000000000000 : ℝ), (34224428575567/100000000000000 : ℝ), (534756648581/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4123986383/10000000000 : ℝ)|^4411 ≤ (7887786476051/25000000000000 : ℝ)^3387
        have hw : |(4123986383/10000000000 : ℝ)|=(4123986383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(137179317/312500000 : ℝ)|^4411 ≤ (34224428575567/100000000000000 : ℝ)^3387
        have hw : |(137179317/312500000 : ℝ)|=(137179317/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2194868921/5000000000 : ℝ)|^4411 ≤ (534756648581/1562500000000 : ℝ)^3387
        have hw : |(2194868921/5000000000 : ℝ)|=(2194868921/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1451_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (2205/512 : ℝ) ≤ p) (hpb : p ≤ (4411/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (159039209/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (923/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2277/20000 : ℝ)*pair X i i ≤ pair X i h) :
    -(31457/50000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(29579/50000 : ℝ) ∧ (80569/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (84767/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (923/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2277/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (923/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2277/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (923/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2277/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (923/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2277/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (923/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2277/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (923/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2277/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2277/20000 : ℝ) ^ (2205/512 : ℝ) ≤ (4314550098611037/50000000000000000000 : ℝ) := by
    have hpowers : (2277/20000 : ℝ)^2205 ≤ (4314550098611037/50000000000000000000 : ℝ)^512 := by
      have hnat : (2277 : ℕ)^2205*50000000000000000000^512 ≤ 4314550098611037^512*20000^2205 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2277 20000 4314550098611037 50000000000000000000 2205 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2277/20000 : ℝ)) (X := (4314550098611037/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2205 512 (by norm_num) hpowers
    exact h
  have hpowhi : (923/6250 : ℝ) ^ (2205/512 : ℝ) ≤ (165366309376521/625000000000000000 : ℝ) := by
    have hpowers : (923/6250 : ℝ)^2205 ≤ (165366309376521/625000000000000000 : ℝ)^512 := by
      have hnat : (923 : ℕ)^2205*625000000000000000^512 ≤ 165366309376521^512*6250^2205 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        923 6250 165366309376521 625000000000000000 2205 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (923/6250 : ℝ)) (X := (165366309376521/625000000000000000 : ℝ)) (by norm_num) (by norm_num) 2205 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (25004314550098611037/25000000000000000000 : ℝ) ≤ (5000200354041397/5000000000000000 : ℝ) ^ (2205/512 : ℝ) := by
    have hpowers : (25004314550098611037/25000000000000000000 : ℝ)^512 ≤ (5000200354041397/5000000000000000 : ℝ)^2205 := by
      have hnat : (25004314550098611037 : ℕ)^512*5000000000000000^2205 ≤ 5000200354041397^2205*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25004314550098611037 25000000000000000000 5000200354041397 5000000000000000 512 2205 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000200354041397/5000000000000000 : ℝ)) (X := (25004314550098611037/25000000000000000000 : ℝ)) (by norm_num) 2205 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (50017543854848732717/50000000000000000000 : ℝ) ≤ (1000081462530431/1000000000000000 : ℝ) ^ (2205/512 : ℝ) := by
    have hpowers : (50017543854848732717/50000000000000000000 : ℝ)^512 ≤ (1000081462530431/1000000000000000 : ℝ)^2205 := by
      have hnat : (50017543854848732717 : ℕ)^512*1000000000000000^2205 ≤ 1000081462530431^2205*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50017543854848732717 50000000000000000000 1000081462530431 1000000000000000 512 2205 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000081462530431/1000000000000000 : ℝ)) (X := (50017543854848732717/50000000000000000000 : ℝ)) (by norm_num) 2205 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (312665366309376521/312500000000000000 : ℝ) ≤ (5000614271262913/5000000000000000 : ℝ) ^ (2205/512 : ℝ) := by
    have hpowers : (312665366309376521/312500000000000000 : ℝ)^512 ≤ (5000614271262913/5000000000000000 : ℝ)^2205 := by
      have hnat : (312665366309376521 : ℕ)^512*5000000000000000^2205 ≤ 5000614271262913^2205*312500000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        312665366309376521 312500000000000000 5000614271262913 5000000000000000 512 2205 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000614271262913/5000000000000000 : ℝ)) (X := (312665366309376521/312500000000000000 : ℝ)) (by norm_num) 2205 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4314550098611037/50000000000000000000 : ℝ) ≤ ((16910965350155086391/16915000000000000000 : ℝ)+2*(103479305379/84575000000000 : ℝ)*(2277/20000 : ℝ))^(2205/512 : ℝ) := by
    rw [show (16910965350155086391/16915000000000000000 : ℝ)+2*(103479305379/84575000000000 : ℝ)*(2277/20000 : ℝ)=(5000200354041397/5000000000000000 : ℝ) by norm_num, show 1+2*(4314550098611037/50000000000000000000 : ℝ)=(25004314550098611037/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(165366309376521/625000000000000000 : ℝ)+(4314550098611037/50000000000000000000 : ℝ) ≤ ((16910965350155086391/16915000000000000000 : ℝ)+(103479305379/84575000000000 : ℝ)*((923/6250 : ℝ)+(2277/20000 : ℝ)))^(2205/512 : ℝ) := by
    rw [show (16910965350155086391/16915000000000000000 : ℝ)+(103479305379/84575000000000 : ℝ)*((923/6250 : ℝ)+(2277/20000 : ℝ))=(1000081462530431/1000000000000000 : ℝ) by norm_num, show 1+(165366309376521/625000000000000000 : ℝ)+(4314550098611037/50000000000000000000 : ℝ)=(50017543854848732717/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(165366309376521/625000000000000000 : ℝ) ≤ ((16910965350155086391/16915000000000000000 : ℝ)+2*(103479305379/84575000000000 : ℝ)*(923/6250 : ℝ))^(2205/512 : ℝ) := by
    rw [show (16910965350155086391/16915000000000000000 : ℝ)+2*(103479305379/84575000000000 : ℝ)*(923/6250 : ℝ)=(5000614271262913/5000000000000000 : ℝ) by norm_num, show 1+2*(165366309376521/625000000000000000 : ℝ)=(312665366309376521/312500000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (16910965350155086391/16915000000000000000 : ℝ)*(X 1 0+X 2 0)+(103479305379/84575000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2205/512 : ℝ)) (lo := (2277/20000 : ℝ)) (hi := (923/6250 : ℝ)) (c := (16910965350155086391/16915000000000000000 : ℝ)) (alpha := (103479305379/84575000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (16910965350155086391/16915000000000000000 : ℝ)*(X 0 1+X 2 1)+(103479305379/84575000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2205/512 : ℝ)) (lo := (2277/20000 : ℝ)) (hi := (923/6250 : ℝ)) (c := (16910965350155086391/16915000000000000000 : ℝ)) (alpha := (103479305379/84575000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (16910965350155086391/16915000000000000000 : ℝ)*(X 0 2+X 1 2)+(103479305379/84575000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2205/512 : ℝ)) (lo := (2277/20000 : ℝ)) (hi := (923/6250 : ℝ)) (c := (16910965350155086391/16915000000000000000 : ℝ)) (alpha := (103479305379/84575000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-358865829/2000000000 : ℝ)*X 0 0+(1346328113/2500000000 : ℝ)*X 0 1+(5385312741/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1451_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2643102199/5000000000 : ℝ)*X 1 0+(-386115181/2000000000 : ℝ)*X 1 1+(107706261/200000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1451_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2643102501/5000000000 : ℝ)*X 2 0+(538531261/1000000000 : ℝ)*X 2 1+(-386115137/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1451_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4444770989/10000000000 : ℝ)*X 0 0+(4229636819/10000000000 : ℝ)*X 0 1+(422963717/1000000000 : ℝ)*X 0 2+(4444770989/10000000000 : ℝ)*X 1 0+(4229636819/10000000000 : ℝ)*X 1 1+(422963717/1000000000 : ℝ)*X 1 2+(4444770989/10000000000 : ℝ)*X 2 0+(4229636819/10000000000 : ℝ)*X 2 1+(422963717/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1451_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-132202523/625000000 : ℝ)*X 0 0+(5266832349/10000000000 : ℝ)*X 0 1+(5266832331/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1451_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5369049301/10000000000 : ℝ)*X 1 0+(-989408089/5000000000 : ℝ)*X 1 1+(2633416157/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1451_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5369049459/10000000000 : ℝ)*X 2 0+(5266832251/10000000000 : ℝ)*X 2 1+(-39576321/200000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1451_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4151958859/10000000000 : ℝ)*X 0 0+(4375992659/10000000000 : ℝ)*X 0 1+(2187996453/5000000000 : ℝ)*X 0 2+(4151958859/10000000000 : ℝ)*X 1 0+(4375992659/10000000000 : ℝ)*X 1 1+(2187996453/5000000000 : ℝ)*X 1 2+(4151958859/10000000000 : ℝ)*X 2 0+(4375992659/10000000000 : ℝ)*X 2 1+(2187996453/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1451_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-51190011/250000000 : ℝ)*X 0 0+(324048951/625000000 : ℝ)*X 0 1+(5399272997/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1451_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((1319109943/2500000000 : ℝ)*X 1 0+(-192476703/1000000000 : ℝ)*X 1 1+(2699636369/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1451_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5276439971/10000000000 : ℝ)*X 2 0+(2699636237/5000000000 : ℝ)*X 2 1+(-24059589/125000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1451_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((447871613/1000000000 : ℝ)*X 0 0+(4212377281/10000000000 : ℝ)*X 0 1+(1053094387/2500000000 : ℝ)*X 0 2+(447871613/1000000000 : ℝ)*X 1 0+(4212377281/10000000000 : ℝ)*X 1 1+(1053094387/2500000000 : ℝ)*X 1 2+(447871613/1000000000 : ℝ)*X 2 0+(4212377281/10000000000 : ℝ)*X 2 1+(1053094387/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1451_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1862113201/10000000000 : ℝ)*X 0 0+(1366344917/2500000000 : ℝ)*X 0 1+(5255695939/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1451_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5376834663/10000000000 : ℝ)*X 1 0+(-991625787/5000000000 : ℝ)*X 1 1+(1313924017/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1451_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((2688417271/5000000000 : ℝ)*X 2 0+(5255696117/10000000000 : ℝ)*X 2 1+(-1983251671/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1451_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((4123986383/10000000000 : ℝ)*X 0 0+(137179317/312500000 : ℝ)*X 0 1+(2194868921/5000000000 : ℝ)*X 0 2+(4123986383/10000000000 : ℝ)*X 1 0+(137179317/312500000 : ℝ)*X 1 1+(2194868921/5000000000 : ℝ)*X 1 2+(4123986383/10000000000 : ℝ)*X 2 0+(137179317/312500000 : ℝ)*X 2 1+(2194868921/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1451_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-31457/50000 : ℝ) ≤ (-21282813670148193243771348286407/33830000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (423333/1000000000000 : ℝ)*(upper0) + (13621851/50000000000000 : ℝ)*(lower1) + (71341239/100000000000000 : ℝ)*(lower2) + (5405249/20000000000000 : ℝ)*(lower3) + (253499/20000000000000 : ℝ)*(upper5) + (121626142355847/4000000000000 : ℝ)*(major0) + (121626142355847/4000000000000 : ℝ)*(major1) + (121626142355847/4000000000000 : ℝ)*(major2) + (619604257/100000000000000 : ℝ)*(sp1) + (2095194105692027/50000000000000 : ℝ)*(sp4) + (2095193795889899/50000000000000 : ℝ)*(sp5) + (2095194105692027/50000000000000 : ℝ)*(sp6) + (238984100246873/12500000000000 : ℝ)*(sp7) + (4114952091/25000000000000 : ℝ)*(sp15) + (477972315445837/25000000000000 : ℝ)*(f.failure) + (2095194105692027/50000000000000 : ℝ)*(f.sum) + (989438069163/211437500000000000000000000 : ℝ)*base66 + (179801107888301823/67660000000000000000000000000000 : ℝ)*base68 + (604082228021981823/67660000000000000000000000000000 : ℝ)*base70 + (560577543972741823/67660000000000000000000000000000 : ℝ)*base72 + (3999577058809/3383000000000000000000000000 : ℝ)*base74 + (879552918459661823/67660000000000000000000000000000 : ℝ)*base76 + (330478286186061823/67660000000000000000000000000000 : ℝ)*base78 + (537341088711581823/67660000000000000000000000000000 : ℝ)*base80 + (733083998393/105718750000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (23822933/2500000000000000000000 : ℝ)*base89 + (23822933/2500000000000000000000 : ℝ)*base91 + (23822933/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (29579/50000 : ℝ) ≤ (500345699162268124853934384104787/845750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (71188847/100000000000000 : ℝ)*(lower1) + (37019879/50000000000000 : ℝ)*(lower3) + (31504891/20000000000000 : ℝ)*(upper4) + (1494581/2000000000000 : ℝ)*(upper5) + (3113003322726173/100000000000000 : ℝ)*(major0) + (3113003322726173/100000000000000 : ℝ)*(major1) + (3113003322726173/100000000000000 : ℝ)*(major2) + (424890560574051/10000000000000 : ℝ)*(sp0) + (424889428389201/10000000000000 : ℝ)*(sp1) + (1062225041045501/25000000000000 : ℝ)*(sp2) + (1957379806024769/100000000000000 : ℝ)*(sp3) + (22643697/200000000000 : ℝ)*(sp5) + (616860037/50000000000000 : ℝ)*(sp7) + (2720779253/50000000000000 : ℝ)*(sp10) + (978690519872421/50000000000000 : ℝ)*(f.failure) + (424890560574051/10000000000000 : ℝ)*(f.sum) + (6187519612613/16915000000000000000000000000 : ℝ)*base65 + (5205511142210288357/1691500000000000000000000000000000 : ℝ)*base68 + (32329660183620788357/1691500000000000000000000000000000 : ℝ)*base70 + (3139146815545288357/1691500000000000000000000000000000 : ℝ)*base72 + (31758853385937/16915000000000000000000000000 : ℝ)*base74 + (30660693653105788357/1691500000000000000000000000000000 : ℝ)*base76 + (16002444182086288357/1691500000000000000000000000000000 : ℝ)*base78 + (9263087709016288357/1691500000000000000000000000000000 : ℝ)*base80 + (89413234759021/8457500000000000000000000000 : ℝ)*base82 + (33245011/5000000000000000000000 : ℝ)*base90 + (33245011/5000000000000000000000 : ℝ)*base92 + (33245011/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (80569/100000 : ℝ) ≤ (340716128385808407072751768851807/422875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (22464127/50000000000000 : ℝ)*(upper0) + (6527549/12500000000000 : ℝ)*(lower3) + (26504941/100000000000000 : ℝ)*(lower5) + (3419654126937259/100000000000000 : ℝ)*(major0) + (3419654126937259/100000000000000 : ℝ)*(major1) + (3419654126937259/100000000000000 : ℝ)*(major2) + (2920301817/100000000000000 : ℝ)*(sp0) + (19003059491/20000000000000 : ℝ)*(sp1) + (2767012519/4000000000000 : ℝ)*(sp3) + (4662238853839249/100000000000000 : ℝ)*(sp8) + (29138503038861/625000000000 : ℝ)*(sp9) + (932451100303043/20000000000000 : ℝ)*(sp10) + (107506322892573/5000000000000 : ℝ)*(sp11) + (13727374149/100000000000000 : ℝ)*(sp12) + (430039126632887/20000000000000 : ℝ)*(f.failure) + (932451100303043/20000000000000 : ℝ)*(f.sum) + (10185179318771/16915000000000000000000000000 : ℝ)*base66 + (8055000831113557731/1691500000000000000000000000000000 : ℝ)*base68 + (22215582539262557731/1691500000000000000000000000000000 : ℝ)*base70 + (11461699591863557731/1691500000000000000000000000000000 : ℝ)*base72 + (167347757483753/8457500000000000000000000000 : ℝ)*base74 + (9951909951976057731/1691500000000000000000000000000000 : ℝ)*base76 + (12941256257246057731/1691500000000000000000000000000000 : ℝ)*base78 + (4457499456021442269/1691500000000000000000000000000000 : ℝ)*base79 + (45971957596403/8457500000000000000000000000 : ℝ)*base82 + (1866383/2000000000000000000000 : ℝ)*base89 + (1866383/2000000000000000000000 : ℝ)*base91 + (1866383/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-84767/100000 : ℝ) ≤ (-17922373711660467293889550327833/21143750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1880171/6250000000000 : ℝ)*(lower0) + (98210739/100000000000000 : ℝ)*(upper3) + (28946423/100000000000000 : ℝ)*(lower4) + (172868838651329/5000000000000 : ℝ)*(major0) + (172868838651329/5000000000000 : ℝ)*(major1) + (172868838651329/5000000000000 : ℝ)*(major2) + (992468697/25000000000000 : ℝ)*(sp0) + (39576029423/50000000000000 : ℝ)*(sp5) + (1688518069/4000000000000 : ℝ)*(sp6) + (2236023653/6250000000000 : ℝ)*(sp7) + (596136207353903/12500000000000 : ℝ)*(sp12) + (2384507238323583/50000000000000 : ℝ)*(sp13) + (4769051415754287/100000000000000 : ℝ)*(sp14) + (86955157694661/4000000000000 : ℝ)*(sp15) + (2173914718744973/100000000000000 : ℝ)*(f.failure) + (1192273407176503/25000000000000 : ℝ)*(f.sum) + (4780881926447/3383000000000000000000000000 : ℝ)*base65 + (394952969667836361/84575000000000000000000000000000 : ℝ)*base68 + (740437181117513639/84575000000000000000000000000000 : ℝ)*base69 + (211232809090161361/84575000000000000000000000000000 : ℝ)*base72 + (406397581539/211437500000000000000000000 : ℝ)*base74 + (313166003995086361/84575000000000000000000000000000 : ℝ)*base76 + (146437078899536361/84575000000000000000000000000000 : ℝ)*base78 + (137648142160786361/84575000000000000000000000000000 : ℝ)*base80 + (13347776346543/3383000000000000000000000000 : ℝ)*base81 + (21353643/10000000000000000000000 : ℝ)*base90 + (21353643/10000000000000000000000 : ℝ)*base92 + (21353643/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1451_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (2205/512 : ℝ) ≤ p) (hpb : p ≤ (4411/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (159039209/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (923/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2277/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31457/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(29579/50000 : ℝ) else (80569/100000 : ℝ) ≤ X j i ∧ X j i ≤ (84767/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1451_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1451_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2205/512 : ℝ) ≤ p) (hpb : p ≤ (4411/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (159039209/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14771/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11381/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31457/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(29579/50000 : ℝ) else (80569/100000 : ℝ) ≤ X j i ∧ X j i ≤ (84767/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1451_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1451_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1451_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2205/512 : ℝ) ≤ p) (hpb : p ≤ (4411/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (159039209/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14771/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11381/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31457/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(29579/50000 : ℝ) else (80569/100000 : ℝ) ≤ X j i ∧ X j i ≤ (84767/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1451_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
