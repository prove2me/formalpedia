-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1607_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:50:54.85773+00:00
-- url     : https://prove2.me/submissions/278c1d77-593d-491a-8d68-ab259cc0f590

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
theorem support_rectangle_w1607_s0_0 (p : ℝ) (hpa : (4743/1024 : ℝ) ≤ p) (hpb : p ≤ (4747/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-98200391/625000000 : ℝ)*x 0 + (730149629/1250000000 : ℝ)*x 1 + (2445378301/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (98200391/625000000 : ℝ)^4747 ≤ (9444077632467/100000000000000 : ℝ)^3723 := by
    have hnat : (98200391 : ℕ)^4747*100000000000000^3723 ≤ 9444077632467^3723*625000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      98200391 625000000 9444077632467 100000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (730149629/1250000000 : ℝ)^4747 ≤ (25191202265433/50000000000000 : ℝ)^3723 := by
    have hnat : (730149629 : ℕ)^4747*50000000000000^3723 ≤ 25191202265433^3723*1250000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      730149629 1250000000 25191202265433 50000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2445378301/5000000000 : ℝ)^4747 ≤ (10043379454437/25000000000000 : ℝ)^3723 := by
    have hnat : (2445378301 : ℕ)^4747*25000000000000^3723 ≤ 10043379454437^3723*5000000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2445378301 5000000000 10043379454437 25000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4747/1024 : ℝ)) 4747 3723 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-98200391/625000000 : ℝ), (730149629/1250000000 : ℝ), (2445378301/5000000000 : ℝ)] ![(9444077632467/100000000000000 : ℝ), (25191202265433/50000000000000 : ℝ), (10043379454437/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-98200391/625000000 : ℝ)|^4747 ≤ (9444077632467/100000000000000 : ℝ)^3723
        have hw : |(-98200391/625000000 : ℝ)|=(98200391/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(730149629/1250000000 : ℝ)|^4747 ≤ (25191202265433/50000000000000 : ℝ)^3723
        have hw : |(730149629/1250000000 : ℝ)|=(730149629/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2445378301/5000000000 : ℝ)|^4747 ≤ (10043379454437/25000000000000 : ℝ)^3723
        have hw : |(2445378301/5000000000 : ℝ)|=(2445378301/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1607_s0_1 (p : ℝ) (hpa : (4743/1024 : ℝ) ≤ p) (hpb : p ≤ (4747/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5454956111/10000000000 : ℝ)*x 0 + (-2097791579/10000000000 : ℝ)*x 1 + (2445378219/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5454956111/10000000000 : ℝ)^4747 ≤ (46173892263321/100000000000000 : ℝ)^3723 := by
    have hnat : (5454956111 : ℕ)^4747*100000000000000^3723 ≤ 46173892263321^3723*10000000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5454956111 10000000000 46173892263321 100000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2097791579/10000000000 : ℝ)^4747 ≤ (1365259162883/10000000000000 : ℝ)^3723 := by
    have hnat : (2097791579 : ℕ)^4747*10000000000000^3723 ≤ 1365259162883^3723*10000000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2097791579 10000000000 1365259162883 10000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2445378219/5000000000 : ℝ)^4747 ≤ (40173516100101/100000000000000 : ℝ)^3723 := by
    have hnat : (2445378219 : ℕ)^4747*100000000000000^3723 ≤ 40173516100101^3723*5000000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2445378219 5000000000 40173516100101 100000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4747/1024 : ℝ)) 4747 3723 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5454956111/10000000000 : ℝ), (-2097791579/10000000000 : ℝ), (2445378219/5000000000 : ℝ)] ![(46173892263321/100000000000000 : ℝ), (1365259162883/10000000000000 : ℝ), (40173516100101/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5454956111/10000000000 : ℝ)|^4747 ≤ (46173892263321/100000000000000 : ℝ)^3723
        have hw : |(5454956111/10000000000 : ℝ)|=(5454956111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2097791579/10000000000 : ℝ)|^4747 ≤ (1365259162883/10000000000000 : ℝ)^3723
        have hw : |(-2097791579/10000000000 : ℝ)|=(2097791579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2445378219/5000000000 : ℝ)|^4747 ≤ (40173516100101/100000000000000 : ℝ)^3723
        have hw : |(2445378219/5000000000 : ℝ)|=(2445378219/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1607_s0_2 (p : ℝ) (hpa : (4743/1024 : ℝ) ≤ p) (hpb : p ≤ (4747/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (272747799/500000000 : ℝ)*x 0 + (4890756521/10000000000 : ℝ)*x 1 + (-524447911/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (272747799/500000000 : ℝ)^4747 ≤ (46173890849473/100000000000000 : ℝ)^3723 := by
    have hnat : (272747799 : ℕ)^4747*100000000000000^3723 ≤ 46173890849473^3723*500000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      272747799 500000000 46173890849473 100000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4890756521/10000000000 : ℝ)^4747 ≤ (20086758484699/50000000000000 : ℝ)^3723 := by
    have hnat : (4890756521 : ℕ)^4747*50000000000000^3723 ≤ 20086758484699^3723*10000000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4890756521 10000000000 20086758484699 50000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (524447911/2500000000 : ℝ)^4747 ≤ (13652592168207/100000000000000 : ℝ)^3723 := by
    have hnat : (524447911 : ℕ)^4747*100000000000000^3723 ≤ 13652592168207^3723*2500000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524447911 2500000000 13652592168207 100000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4747/1024 : ℝ)) 4747 3723 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(272747799/500000000 : ℝ), (4890756521/10000000000 : ℝ), (-524447911/2500000000 : ℝ)] ![(46173890849473/100000000000000 : ℝ), (20086758484699/50000000000000 : ℝ), (13652592168207/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(272747799/500000000 : ℝ)|^4747 ≤ (46173890849473/100000000000000 : ℝ)^3723
        have hw : |(272747799/500000000 : ℝ)|=(272747799/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4890756521/10000000000 : ℝ)|^4747 ≤ (20086758484699/50000000000000 : ℝ)^3723
        have hw : |(4890756521/10000000000 : ℝ)|=(4890756521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-524447911/2500000000 : ℝ)|^4747 ≤ (13652592168207/100000000000000 : ℝ)^3723
        have hw : |(-524447911/2500000000 : ℝ)|=(524447911/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1607_s0_3 (p : ℝ) (hpa : (4743/1024 : ℝ) ≤ p) (hpb : p ≤ (4747/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2055627661/5000000000 : ℝ)*x 0 + (3073811537/10000000000 : ℝ)*x 1 + (216005819/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2055627661/5000000000 : ℝ)^4747 ≤ (503059439873/1562500000000 : ℝ)^3723 := by
    have hnat : (2055627661 : ℕ)^4747*1562500000000^3723 ≤ 503059439873^3723*5000000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2055627661 5000000000 503059439873 1562500000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3073811537/10000000000 : ℝ)^4747 ≤ (4444208136781/20000000000000 : ℝ)^3723 := by
    have hnat : (3073811537 : ℕ)^4747*20000000000000^3723 ≤ 4444208136781^3723*10000000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3073811537 10000000000 4444208136781 20000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (216005819/400000000 : ℝ)^4747 ≤ (1424473598051/3125000000000 : ℝ)^3723 := by
    have hnat : (216005819 : ℕ)^4747*3125000000000^3723 ≤ 1424473598051^3723*400000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216005819 400000000 1424473598051 3125000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4747/1024 : ℝ)) 4747 3723 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2055627661/5000000000 : ℝ), (3073811537/10000000000 : ℝ), (216005819/400000000 : ℝ)] ![(503059439873/1562500000000 : ℝ), (4444208136781/20000000000000 : ℝ), (1424473598051/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2055627661/5000000000 : ℝ)|^4747 ≤ (503059439873/1562500000000 : ℝ)^3723
        have hw : |(2055627661/5000000000 : ℝ)|=(2055627661/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3073811537/10000000000 : ℝ)|^4747 ≤ (4444208136781/20000000000000 : ℝ)^3723
        have hw : |(3073811537/10000000000 : ℝ)|=(3073811537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(216005819/400000000 : ℝ)|^4747 ≤ (1424473598051/3125000000000 : ℝ)^3723
        have hw : |(216005819/400000000 : ℝ)|=(216005819/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1607_s0_4 (p : ℝ) (hpa : (4743/1024 : ℝ) ≤ p) (hpb : p ≤ (4747/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-787020087/5000000000 : ℝ)*x 0 + (4914848579/10000000000 : ℝ)*x 1 + (5816248011/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (787020087/5000000000 : ℝ)^4747 ≤ (9465802017349/100000000000000 : ℝ)^3723 := by
    have hnat : (787020087 : ℕ)^4747*100000000000000^3723 ≤ 9465802017349^3723*5000000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      787020087 5000000000 9465802017349 100000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4914848579/10000000000 : ℝ)^4747 ≤ (631656481409/1562500000000 : ℝ)^3723 := by
    have hnat : (4914848579 : ℕ)^4747*1562500000000^3723 ≤ 631656481409^3723*10000000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4914848579 10000000000 631656481409 1562500000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5816248011/10000000000 : ℝ)^4747 ≤ (50108183159427/100000000000000 : ℝ)^3723 := by
    have hnat : (5816248011 : ℕ)^4747*100000000000000^3723 ≤ 50108183159427^3723*10000000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5816248011 10000000000 50108183159427 100000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4747/1024 : ℝ)) 4747 3723 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-787020087/5000000000 : ℝ), (4914848579/10000000000 : ℝ), (5816248011/10000000000 : ℝ)] ![(9465802017349/100000000000000 : ℝ), (631656481409/1562500000000 : ℝ), (50108183159427/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-787020087/5000000000 : ℝ)|^4747 ≤ (9465802017349/100000000000000 : ℝ)^3723
        have hw : |(-787020087/5000000000 : ℝ)|=(787020087/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4914848579/10000000000 : ℝ)|^4747 ≤ (631656481409/1562500000000 : ℝ)^3723
        have hw : |(4914848579/10000000000 : ℝ)|=(4914848579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5816248011/10000000000 : ℝ)|^4747 ≤ (50108183159427/100000000000000 : ℝ)^3723
        have hw : |(5816248011/10000000000 : ℝ)|=(5816248011/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1607_s0_5 (p : ℝ) (hpa : (4743/1024 : ℝ) ≤ p) (hpb : p ≤ (4747/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5195371193/10000000000 : ℝ)*x 0 + (-586149529/5000000000 : ℝ)*x 1 + (2908124201/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5195371193/10000000000 : ℝ)^4747 ≤ (21695405856123/50000000000000 : ℝ)^3723 := by
    have hnat : (5195371193 : ℕ)^4747*50000000000000^3723 ≤ 21695405856123^3723*10000000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5195371193 10000000000 21695405856123 50000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (586149529/5000000000 : ℝ)^4747 ≤ (10157813773/156250000000 : ℝ)^3723 := by
    have hnat : (586149529 : ℕ)^4747*156250000000^3723 ≤ 10157813773^3723*5000000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      586149529 5000000000 10157813773 156250000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2908124201/5000000000 : ℝ)^4747 ≤ (50108187454481/100000000000000 : ℝ)^3723 := by
    have hnat : (2908124201 : ℕ)^4747*100000000000000^3723 ≤ 50108187454481^3723*5000000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2908124201 5000000000 50108187454481 100000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4747/1024 : ℝ)) 4747 3723 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5195371193/10000000000 : ℝ), (-586149529/5000000000 : ℝ), (2908124201/5000000000 : ℝ)] ![(21695405856123/50000000000000 : ℝ), (10157813773/156250000000 : ℝ), (50108187454481/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5195371193/10000000000 : ℝ)|^4747 ≤ (21695405856123/50000000000000 : ℝ)^3723
        have hw : |(5195371193/10000000000 : ℝ)|=(5195371193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-586149529/5000000000 : ℝ)|^4747 ≤ (10157813773/156250000000 : ℝ)^3723
        have hw : |(-586149529/5000000000 : ℝ)|=(586149529/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2908124201/5000000000 : ℝ)|^4747 ≤ (50108187454481/100000000000000 : ℝ)^3723
        have hw : |(2908124201/5000000000 : ℝ)|=(2908124201/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1607_s0_6 (p : ℝ) (hpa : (4743/1024 : ℝ) ≤ p) (hpb : p ≤ (4747/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5195371391/10000000000 : ℝ)*x 0 + (1454061991/2500000000 : ℝ)*x 1 + (-586149721/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5195371391/10000000000 : ℝ)^4747 ≤ (43390813820741/100000000000000 : ℝ)^3723 := by
    have hnat : (5195371391 : ℕ)^4747*100000000000000^3723 ≤ 43390813820741^3723*10000000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5195371391 10000000000 43390813820741 100000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1454061991/2500000000 : ℝ)^4747 ≤ (50108182643141/100000000000000 : ℝ)^3723 := by
    have hnat : (1454061991 : ℕ)^4747*100000000000000^3723 ≤ 50108182643141^3723*2500000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1454061991 2500000000 50108182643141 100000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (586149721/5000000000 : ℝ)^4747 ≤ (406312720619/6250000000000 : ℝ)^3723 := by
    have hnat : (586149721 : ℕ)^4747*6250000000000^3723 ≤ 406312720619^3723*5000000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      586149721 5000000000 406312720619 6250000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4747/1024 : ℝ)) 4747 3723 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5195371391/10000000000 : ℝ), (1454061991/2500000000 : ℝ), (-586149721/5000000000 : ℝ)] ![(43390813820741/100000000000000 : ℝ), (50108182643141/100000000000000 : ℝ), (406312720619/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5195371391/10000000000 : ℝ)|^4747 ≤ (43390813820741/100000000000000 : ℝ)^3723
        have hw : |(5195371391/10000000000 : ℝ)|=(5195371391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1454061991/2500000000 : ℝ)|^4747 ≤ (50108182643141/100000000000000 : ℝ)^3723
        have hw : |(1454061991/2500000000 : ℝ)|=(1454061991/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-586149721/5000000000 : ℝ)|^4747 ≤ (406312720619/6250000000000 : ℝ)^3723
        have hw : |(-586149721/5000000000 : ℝ)|=(586149721/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1607_s0_7 (p : ℝ) (hpa : (4743/1024 : ℝ) ≤ p) (hpb : p ≤ (4747/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4118193781/10000000000 : ℝ)*x 0 + (1335294609/2500000000 : ℝ)*x 1 + (3134876561/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4118193781/10000000000 : ℝ)^4747 ≤ (4033137651189/12500000000000 : ℝ)^3723 := by
    have hnat : (4118193781 : ℕ)^4747*12500000000000^3723 ≤ 4033137651189^3723*10000000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4118193781 10000000000 4033137651189 12500000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1335294609/2500000000 : ℝ)^4747 ≤ (44949460487423/100000000000000 : ℝ)^3723 := by
    have hnat : (1335294609 : ℕ)^4747*100000000000000^3723 ≤ 44949460487423^3723*2500000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1335294609 2500000000 44949460487423 100000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3134876561/10000000000 : ℝ)^4747 ≤ (22785438285353/100000000000000 : ℝ)^3723 := by
    have hnat : (3134876561 : ℕ)^4747*100000000000000^3723 ≤ 22785438285353^3723*10000000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3134876561 10000000000 22785438285353 100000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4747/1024 : ℝ)) 4747 3723 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4118193781/10000000000 : ℝ), (1335294609/2500000000 : ℝ), (3134876561/10000000000 : ℝ)] ![(4033137651189/12500000000000 : ℝ), (44949460487423/100000000000000 : ℝ), (22785438285353/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4118193781/10000000000 : ℝ)|^4747 ≤ (4033137651189/12500000000000 : ℝ)^3723
        have hw : |(4118193781/10000000000 : ℝ)|=(4118193781/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1335294609/2500000000 : ℝ)|^4747 ≤ (44949460487423/100000000000000 : ℝ)^3723
        have hw : |(1335294609/2500000000 : ℝ)|=(1335294609/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3134876561/10000000000 : ℝ)|^4747 ≤ (22785438285353/100000000000000 : ℝ)^3723
        have hw : |(3134876561/10000000000 : ℝ)|=(3134876561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1607_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4743/1024 : ℝ) ≤ p) (hpb : p ≤ (4747/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (2154773/1250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (3957/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (24311/100000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4743/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4743 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4743*1^1024 ≤ 0^1024*1^4743 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4743 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4743 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4743/1024 : ℝ) ≤ (1434852196418327073/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4743 ≤ (1434852196418327073/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4743*100000000000000000000^1024 ≤ 1434852196418327073^1024*5^4743 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 1434852196418327073 100000000000000000000 4743 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (1434852196418327073/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4743 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4743/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4743 := by
      have hnat : (1 : ℕ)^1024*1^4743 ≤ 1^4743*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4743 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4743 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (101434852196418327073/100000000000000000000 : ℝ) ≤ (10030805254160231/10000000000000000 : ℝ) ^ (4743/1024 : ℝ) := by
    have hpowers : (101434852196418327073/100000000000000000000 : ℝ)^1024 ≤ (10030805254160231/10000000000000000 : ℝ)^4743 := by
      have hnat : (101434852196418327073 : ℕ)^1024*10000000000000000^4743 ≤ 10030805254160231^4743*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        101434852196418327073 100000000000000000000 10030805254160231 10000000000000000 1024 4743 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10030805254160231/10000000000000000 : ℝ)) (X := (101434852196418327073/100000000000000000000 : ℝ)) (by norm_num) 4743 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (51434852196418327073/50000000000000000000 : ℝ) ≤ (5030805254160231/5000000000000000 : ℝ) ^ (4743/1024 : ℝ) := by
    have hpowers : (51434852196418327073/50000000000000000000 : ℝ)^1024 ≤ (5030805254160231/5000000000000000 : ℝ)^4743 := by
      have hnat : (51434852196418327073 : ℕ)^1024*5000000000000000^4743 ≤ 5030805254160231^4743*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51434852196418327073 50000000000000000000 5030805254160231 5000000000000000 1024 4743 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5030805254160231/5000000000000000 : ℝ)) (X := (51434852196418327073/50000000000000000000 : ℝ)) (by norm_num) 4743 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(30805254160231/4000000000000000 : ℝ)*(0 : ℝ))^(4743/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(30805254160231/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1434852196418327073/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(30805254160231/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4743/1024 : ℝ) := by
    rw [show (1 : ℝ)+(30805254160231/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10030805254160231/10000000000000000 : ℝ) by norm_num, show 1+(1434852196418327073/100000000000000000000 : ℝ)+(0 : ℝ)=(101434852196418327073/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1434852196418327073/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(30805254160231/4000000000000000 : ℝ)*(2/5 : ℝ))^(4743/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(30805254160231/4000000000000000 : ℝ)*(2/5 : ℝ)=(5030805254160231/5000000000000000 : ℝ) by norm_num, show 1+2*(1434852196418327073/100000000000000000000 : ℝ)=(51434852196418327073/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(30805254160231/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4743/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (30805254160231/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(30805254160231/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4743/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (30805254160231/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(30805254160231/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4743/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (30805254160231/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-98200391/625000000 : ℝ)*X 0 0+(730149629/1250000000 : ℝ)*X 0 1+(2445378301/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1607_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5454956111/10000000000 : ℝ)*X 1 0+(-2097791579/10000000000 : ℝ)*X 1 1+(2445378219/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1607_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((272747799/500000000 : ℝ)*X 2 0+(4890756521/10000000000 : ℝ)*X 2 1+(-524447911/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1607_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2055627661/5000000000 : ℝ)*X 0 0+(3073811537/10000000000 : ℝ)*X 0 1+(216005819/400000000 : ℝ)*X 0 2+(2055627661/5000000000 : ℝ)*X 1 0+(3073811537/10000000000 : ℝ)*X 1 1+(216005819/400000000 : ℝ)*X 1 2+(2055627661/5000000000 : ℝ)*X 2 0+(3073811537/10000000000 : ℝ)*X 2 1+(216005819/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1607_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-787020087/5000000000 : ℝ)*X 0 0+(4914848579/10000000000 : ℝ)*X 0 1+(5816248011/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1607_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5195371193/10000000000 : ℝ)*X 1 0+(-586149529/5000000000 : ℝ)*X 1 1+(2908124201/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1607_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5195371391/10000000000 : ℝ)*X 2 0+(1454061991/2500000000 : ℝ)*X 2 1+(-586149721/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1607_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4118193781/10000000000 : ℝ)*X 0 0+(1335294609/2500000000 : ℝ)*X 0 1+(3134876561/10000000000 : ℝ)*X 0 2+(4118193781/10000000000 : ℝ)*X 1 0+(1335294609/2500000000 : ℝ)*X 1 1+(3134876561/10000000000 : ℝ)*X 1 2+(4118193781/10000000000 : ℝ)*X 2 0+(1335294609/2500000000 : ℝ)*X 2 1+(3134876561/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1607_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (914180707497884963768151/200000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (23429789/100000000000000 : ℝ)*(base1) + (225281307/25000000000000 : ℝ)*(base19) + (875858009/100000000000000 : ℝ)*(base23) + (13313889/10000000000000 : ℝ)*(upper3) + (13243131/12500000000000 : ℝ)*(upper5) + (741007124120631/100000000000000 : ℝ)*(major0) + (741007124120631/100000000000000 : ℝ)*(major1) + (741007124120631/100000000000000 : ℝ)*(major2) + (65759193476597/6250000000000 : ℝ)*(sp0) + (263037349241173/25000000000000 : ℝ)*(sp1) + (131518677778989/12500000000000 : ℝ)*(sp2) + (429862265843041/100000000000000 : ℝ)*(sp3) + (1612947079/50000000000000 : ℝ)*(sp4) + (377128763/25000000000000 : ℝ)*(sp7) + (214931898893941/50000000000000 : ℝ)*(f.failure) + (3287969681531/312500000000 : ℝ)*(f.sum) + (373210444825761/200000000000000000000000000000 : ℝ)*base65 + (2054201912825761/400000000000000000000000000000 : ℝ)*base67 + (232819628774239/400000000000000000000000000000 : ℝ)*base70 + (2558764796425761/400000000000000000000000000000 : ℝ)*base71 + (368529442625761/200000000000000000000000000000 : ℝ)*base73 + (3315271149625761/400000000000000000000000000000 : ℝ)*base75 + (1824924417225761/400000000000000000000000000000 : ℝ)*base77 + (849467910425761/400000000000000000000000000000 : ℝ)*base79 + (227528216974239/200000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (444607/62500000000000000000 : ℝ)*base90 + (444607/62500000000000000000 : ℝ)*base92 + (444607/62500000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1413195741987098163/500000000000000000000000 : ℝ) := by norm_num
    linear_combination (169838627/100000000000000 : ℝ)*(base1) + (561904021/100000000000000 : ℝ)*(base19) + (296929969/50000000000000 : ℝ)*(base23) + (11943623/20000000000000 : ℝ)*(upper3) + (195329144276651/25000000000000 : ℝ)*(major0) + (195329144276651/25000000000000 : ℝ)*(major1) + (195329144276651/25000000000000 : ℝ)*(major2) + (1296209887/100000000000000 : ℝ)*(sp1) + (544795803/50000000000000 : ℝ)*(sp2) + (6319957/10000000000000 : ℝ)*(sp3) + (277346403910777/25000000000000 : ℝ)*(sp4) + (554691793845287/50000000000000 : ℝ)*(sp5) + (554691881176469/50000000000000 : ℝ)*(sp6) + (453247381157477/100000000000000 : ℝ)*(sp7) + (226623807097837/50000000000000 : ℝ)*(f.failure) + (554692722902241/50000000000000 : ℝ)*(f.sum) + (62668881816381/50000000000000000000000000000 : ℝ)*base65 + (84746086666381/100000000000000000000000000000 : ℝ)*base67 + (40109107433619/100000000000000000000000000000 : ℝ)*base70 + (201575685533619/100000000000000000000000000000 : ℝ)*base72 + (143881736216381/50000000000000000000000000000 : ℝ)*base73 + (75269814033619/100000000000000000000000000000 : ℝ)*base76 + (406675325433619/100000000000000000000000000000 : ℝ)*base78 + (260912344066381/100000000000000000000000000000 : ℝ)*base79 + (5101128283619/50000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (26001/62500000000000000000 : ℝ)*base89 + (26001/62500000000000000000 : ℝ)*base91 + (26001/62500000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1607_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4743/1024 : ℝ) ≤ p) (hpb : p ≤ (4747/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (2154773/1250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (3957/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (24311/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1607_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1607_s1_0 (p : ℝ) (hpa : (4743/1024 : ℝ) ≤ p) (hpb : p ≤ (4747/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1696010069/10000000000 : ℝ)*x 0 + (5532733783/10000000000 : ℝ)*x 1 + (5118530827/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1696010069/10000000000 : ℝ)^4747 ≤ (5205411018707/50000000000000 : ℝ)^3723 := by
    have hnat : (1696010069 : ℕ)^4747*50000000000000^3723 ≤ 5205411018707^3723*10000000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1696010069 10000000000 5205411018707 50000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5532733783/10000000000 : ℝ)^4747 ≤ (47014966237559/100000000000000 : ℝ)^3723 := by
    have hnat : (5532733783 : ℕ)^4747*100000000000000^3723 ≤ 47014966237559^3723*10000000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5532733783 10000000000 47014966237559 100000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5118530827/10000000000 : ℝ)^4747 ≤ (21287105855017/50000000000000 : ℝ)^3723 := by
    have hnat : (5118530827 : ℕ)^4747*50000000000000^3723 ≤ 21287105855017^3723*10000000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5118530827 10000000000 21287105855017 50000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4747/1024 : ℝ)) 4747 3723 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1696010069/10000000000 : ℝ), (5532733783/10000000000 : ℝ), (5118530827/10000000000 : ℝ)] ![(5205411018707/50000000000000 : ℝ), (47014966237559/100000000000000 : ℝ), (21287105855017/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1696010069/10000000000 : ℝ)|^4747 ≤ (5205411018707/50000000000000 : ℝ)^3723
        have hw : |(-1696010069/10000000000 : ℝ)|=(1696010069/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5532733783/10000000000 : ℝ)|^4747 ≤ (47014966237559/100000000000000 : ℝ)^3723
        have hw : |(5532733783/10000000000 : ℝ)|=(5532733783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5118530827/10000000000 : ℝ)|^4747 ≤ (21287105855017/50000000000000 : ℝ)^3723
        have hw : |(5118530827/10000000000 : ℝ)|=(5118530827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1607_s1_1 (p : ℝ) (hpa : (4743/1024 : ℝ) ≤ p) (hpb : p ≤ (4747/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5372861907/10000000000 : ℝ)*x 0 + (-1912742749/10000000000 : ℝ)*x 1 + (1023706137/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5372861907/10000000000 : ℝ)^4747 ≤ (1415303498011/3125000000000 : ℝ)^3723 := by
    have hnat : (5372861907 : ℕ)^4747*3125000000000^3723 ≤ 1415303498011^3723*10000000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5372861907 10000000000 1415303498011 3125000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1912742749/10000000000 : ℝ)^4747 ≤ (18962621639/156250000000 : ℝ)^3723 := by
    have hnat : (1912742749 : ℕ)^4747*156250000000^3723 ≤ 18962621639^3723*10000000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1912742749 10000000000 18962621639 156250000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1023706137/2000000000 : ℝ)^4747 ≤ (21287105102033/50000000000000 : ℝ)^3723 := by
    have hnat : (1023706137 : ℕ)^4747*50000000000000^3723 ≤ 21287105102033^3723*2000000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1023706137 2000000000 21287105102033 50000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4747/1024 : ℝ)) 4747 3723 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5372861907/10000000000 : ℝ), (-1912742749/10000000000 : ℝ), (1023706137/2000000000 : ℝ)] ![(1415303498011/3125000000000 : ℝ), (18962621639/156250000000 : ℝ), (21287105102033/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5372861907/10000000000 : ℝ)|^4747 ≤ (1415303498011/3125000000000 : ℝ)^3723
        have hw : |(5372861907/10000000000 : ℝ)|=(5372861907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1912742749/10000000000 : ℝ)|^4747 ≤ (18962621639/156250000000 : ℝ)^3723
        have hw : |(-1912742749/10000000000 : ℝ)|=(1912742749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1023706137/2000000000 : ℝ)|^4747 ≤ (21287105102033/50000000000000 : ℝ)^3723
        have hw : |(1023706137/2000000000 : ℝ)|=(1023706137/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1607_s1_2 (p : ℝ) (hpa : (4743/1024 : ℝ) ≤ p) (hpb : p ≤ (4747/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5372861567/10000000000 : ℝ)*x 0 + (5118530969/10000000000 : ℝ)*x 1 + (-1912742827/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5372861567/10000000000 : ℝ)^4747 ≤ (2830606767631/6250000000000 : ℝ)^3723 := by
    have hnat : (5372861567 : ℕ)^4747*6250000000000^3723 ≤ 2830606767631^3723*10000000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5372861567 10000000000 2830606767631 6250000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5118530969/10000000000 : ℝ)^4747 ≤ (21287106608001/50000000000000 : ℝ)^3723 := by
    have hnat : (5118530969 : ℕ)^4747*50000000000000^3723 ≤ 21287106608001^3723*10000000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5118530969 10000000000 21287106608001 50000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1912742827/10000000000 : ℝ)^4747 ≤ (606803923999/5000000000000 : ℝ)^3723 := by
    have hnat : (1912742827 : ℕ)^4747*5000000000000^3723 ≤ 606803923999^3723*10000000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1912742827 10000000000 606803923999 5000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4747/1024 : ℝ)) 4747 3723 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5372861567/10000000000 : ℝ), (5118530969/10000000000 : ℝ), (-1912742827/10000000000 : ℝ)] ![(2830606767631/6250000000000 : ℝ), (21287106608001/50000000000000 : ℝ), (606803923999/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5372861567/10000000000 : ℝ)|^4747 ≤ (2830606767631/6250000000000 : ℝ)^3723
        have hw : |(5372861567/10000000000 : ℝ)|=(5372861567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5118530969/10000000000 : ℝ)|^4747 ≤ (21287106608001/50000000000000 : ℝ)^3723
        have hw : |(5118530969/10000000000 : ℝ)|=(5118530969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1912742827/10000000000 : ℝ)|^4747 ≤ (606803923999/5000000000000 : ℝ)^3723
        have hw : |(-1912742827/10000000000 : ℝ)|=(1912742827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1607_s1_3 (p : ℝ) (hpa : (4743/1024 : ℝ) ≤ p) (hpb : p ≤ (4747/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (525430833/1250000000 : ℝ)*x 0 + (3720111503/10000000000 : ℝ)*x 1 + (473393011/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (525430833/1250000000 : ℝ)^4747 ≤ (8279791130381/25000000000000 : ℝ)^3723 := by
    have hnat : (525430833 : ℕ)^4747*25000000000000^3723 ≤ 8279791130381^3723*1250000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      525430833 1250000000 8279791130381 25000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3720111503/10000000000 : ℝ)^4747 ≤ (28342532895209/100000000000000 : ℝ)^3723 := by
    have hnat : (3720111503 : ℕ)^4747*100000000000000^3723 ≤ 28342532895209^3723*10000000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3720111503 10000000000 28342532895209 100000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (473393011/1000000000 : ℝ)^4747 ≤ (38538302573509/100000000000000 : ℝ)^3723 := by
    have hnat : (473393011 : ℕ)^4747*100000000000000^3723 ≤ 38538302573509^3723*1000000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      473393011 1000000000 38538302573509 100000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4747/1024 : ℝ)) 4747 3723 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(525430833/1250000000 : ℝ), (3720111503/10000000000 : ℝ), (473393011/1000000000 : ℝ)] ![(8279791130381/25000000000000 : ℝ), (28342532895209/100000000000000 : ℝ), (38538302573509/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(525430833/1250000000 : ℝ)|^4747 ≤ (8279791130381/25000000000000 : ℝ)^3723
        have hw : |(525430833/1250000000 : ℝ)|=(525430833/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3720111503/10000000000 : ℝ)|^4747 ≤ (28342532895209/100000000000000 : ℝ)^3723
        have hw : |(3720111503/10000000000 : ℝ)|=(3720111503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(473393011/1000000000 : ℝ)|^4747 ≤ (38538302573509/100000000000000 : ℝ)^3723
        have hw : |(473393011/1000000000 : ℝ)|=(473393011/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1607_s1_4 (p : ℝ) (hpa : (4743/1024 : ℝ) ≤ p) (hpb : p ≤ (4747/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1696239229/10000000000 : ℝ)*x 0 + (5123064141/10000000000 : ℝ)*x 1 + (2764064927/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1696239229/10000000000 : ℝ)^4747 ≤ (1301576956783/12500000000000 : ℝ)^3723 := by
    have hnat : (1696239229 : ℕ)^4747*12500000000000^3723 ≤ 1301576956783^3723*10000000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1696239229 10000000000 1301576956783 12500000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5123064141/10000000000 : ℝ)^4747 ≤ (42622295221031/100000000000000 : ℝ)^3723 := by
    have hnat : (5123064141 : ℕ)^4747*100000000000000^3723 ≤ 42622295221031^3723*10000000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5123064141 10000000000 42622295221031 100000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2764064927/5000000000 : ℝ)^4747 ≤ (46965089107567/100000000000000 : ℝ)^3723 := by
    have hnat : (2764064927 : ℕ)^4747*100000000000000^3723 ≤ 46965089107567^3723*5000000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2764064927 5000000000 46965089107567 100000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4747/1024 : ℝ)) 4747 3723 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1696239229/10000000000 : ℝ), (5123064141/10000000000 : ℝ), (2764064927/5000000000 : ℝ)] ![(1301576956783/12500000000000 : ℝ), (42622295221031/100000000000000 : ℝ), (46965089107567/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1696239229/10000000000 : ℝ)|^4747 ≤ (1301576956783/12500000000000 : ℝ)^3723
        have hw : |(-1696239229/10000000000 : ℝ)|=(1696239229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5123064141/10000000000 : ℝ)|^4747 ≤ (42622295221031/100000000000000 : ℝ)^3723
        have hw : |(5123064141/10000000000 : ℝ)|=(5123064141/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2764064927/5000000000 : ℝ)|^4747 ≤ (46965089107567/100000000000000 : ℝ)^3723
        have hw : |(2764064927/5000000000 : ℝ)|=(2764064927/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1607_s1_5 (p : ℝ) (hpa : (4743/1024 : ℝ) ≤ p) (hpb : p ≤ (4747/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (263136179/500000000 : ℝ)*x 0 + (-1503143351/10000000000 : ℝ)*x 1 + (221125207/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (263136179/500000000 : ℝ)^4747 ≤ (44109319636191/100000000000000 : ℝ)^3723 := by
    have hnat : (263136179 : ℕ)^4747*100000000000000^3723 ≤ 44109319636191^3723*500000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263136179 500000000 44109319636191 100000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1503143351/10000000000 : ℝ)^4747 ≤ (557849235621/6250000000000 : ℝ)^3723 := by
    have hnat : (1503143351 : ℕ)^4747*6250000000000^3723 ≤ 557849235621^3723*10000000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1503143351 10000000000 557849235621 6250000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (221125207/400000000 : ℝ)^4747 ≤ (23482546292377/50000000000000 : ℝ)^3723 := by
    have hnat : (221125207 : ℕ)^4747*50000000000000^3723 ≤ 23482546292377^3723*400000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      221125207 400000000 23482546292377 50000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4747/1024 : ℝ)) 4747 3723 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(263136179/500000000 : ℝ), (-1503143351/10000000000 : ℝ), (221125207/400000000 : ℝ)] ![(44109319636191/100000000000000 : ℝ), (557849235621/6250000000000 : ℝ), (23482546292377/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(263136179/500000000 : ℝ)|^4747 ≤ (44109319636191/100000000000000 : ℝ)^3723
        have hw : |(263136179/500000000 : ℝ)|=(263136179/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1503143351/10000000000 : ℝ)|^4747 ≤ (557849235621/6250000000000 : ℝ)^3723
        have hw : |(-1503143351/10000000000 : ℝ)|=(1503143351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(221125207/400000000 : ℝ)|^4747 ≤ (23482546292377/50000000000000 : ℝ)^3723
        have hw : |(221125207/400000000 : ℝ)|=(221125207/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1607_s1_6 (p : ℝ) (hpa : (4743/1024 : ℝ) ≤ p) (hpb : p ≤ (4747/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2631361479/5000000000 : ℝ)*x 0 + (5528130409/10000000000 : ℝ)*x 1 + (-1503143893/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2631361479/5000000000 : ℝ)^4747 ≤ (44109312989027/100000000000000 : ℝ)^3723 := by
    have hnat : (2631361479 : ℕ)^4747*100000000000000^3723 ≤ 44109312989027^3723*5000000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2631361479 5000000000 44109312989027 100000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5528130409/10000000000 : ℝ)^4747 ≤ (46965095119527/100000000000000 : ℝ)^3723 := by
    have hnat : (5528130409 : ℕ)^4747*100000000000000^3723 ≤ 46965095119527^3723*10000000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5528130409 10000000000 46965095119527 100000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1503143893/10000000000 : ℝ)^4747 ≤ (8925591873507/100000000000000 : ℝ)^3723 := by
    have hnat : (1503143893 : ℕ)^4747*100000000000000^3723 ≤ 8925591873507^3723*10000000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1503143893 10000000000 8925591873507 100000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4747/1024 : ℝ)) 4747 3723 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2631361479/5000000000 : ℝ), (5528130409/10000000000 : ℝ), (-1503143893/10000000000 : ℝ)] ![(44109312989027/100000000000000 : ℝ), (46965095119527/100000000000000 : ℝ), (8925591873507/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2631361479/5000000000 : ℝ)|^4747 ≤ (44109312989027/100000000000000 : ℝ)^3723
        have hw : |(2631361479/5000000000 : ℝ)|=(2631361479/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5528130409/10000000000 : ℝ)|^4747 ≤ (46965095119527/100000000000000 : ℝ)^3723
        have hw : |(5528130409/10000000000 : ℝ)|=(5528130409/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1503143893/10000000000 : ℝ)|^4747 ≤ (8925591873507/100000000000000 : ℝ)^3723
        have hw : |(-1503143893/10000000000 : ℝ)|=(1503143893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1607_s1_7 (p : ℝ) (hpa : (4743/1024 : ℝ) ≤ p) (hpb : p ≤ (4747/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (168160259/400000000 : ℝ)*x 0 + (2361417669/5000000000 : ℝ)*x 1 + (932844793/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (168160259/400000000 : ℝ)^4747 ≤ (16562394287287/50000000000000 : ℝ)^3723 := by
    have hnat : (168160259 : ℕ)^4747*50000000000000^3723 ≤ 16562394287287^3723*400000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      168160259 400000000 16562394287287 50000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2361417669/5000000000 : ℝ)^4747 ≤ (38423176090323/100000000000000 : ℝ)^3723 := by
    have hnat : (2361417669 : ℕ)^4747*100000000000000^3723 ≤ 38423176090323^3723*5000000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2361417669 5000000000 38423176090323 100000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (932844793/2500000000 : ℝ)^4747 ≤ (28452035313093/100000000000000 : ℝ)^3723 := by
    have hnat : (932844793 : ℕ)^4747*100000000000000^3723 ≤ 28452035313093^3723*2500000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      932844793 2500000000 28452035313093 100000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4747/1024 : ℝ)) 4747 3723 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(168160259/400000000 : ℝ), (2361417669/5000000000 : ℝ), (932844793/2500000000 : ℝ)] ![(16562394287287/50000000000000 : ℝ), (38423176090323/100000000000000 : ℝ), (28452035313093/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(168160259/400000000 : ℝ)|^4747 ≤ (16562394287287/50000000000000 : ℝ)^3723
        have hw : |(168160259/400000000 : ℝ)|=(168160259/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2361417669/5000000000 : ℝ)|^4747 ≤ (38423176090323/100000000000000 : ℝ)^3723
        have hw : |(2361417669/5000000000 : ℝ)|=(2361417669/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(932844793/2500000000 : ℝ)|^4747 ≤ (28452035313093/100000000000000 : ℝ)^3723
        have hw : |(932844793/2500000000 : ℝ)|=(932844793/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1607_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4743/1024 : ℝ) ≤ p) (hpb : p ≤ (4747/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (2154773/1250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (24311/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3957/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2269/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4463/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (24311/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (3957/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (24311/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (3957/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (24311/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (3957/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (24311/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (3957/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (24311/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (3957/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (24311/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (3957/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (3957/100000 : ℝ) ^ (4743/1024 : ℝ) ≤ (1592940920327/5000000000000000000 : ℝ) := by
    have hpowers : (3957/100000 : ℝ)^4743 ≤ (1592940920327/5000000000000000000 : ℝ)^1024 := by
      have hnat : (3957 : ℕ)^4743*5000000000000000000^1024 ≤ 1592940920327^1024*100000^4743 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3957 100000 1592940920327 5000000000000000000 4743 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3957/100000 : ℝ)) (X := (1592940920327/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4743 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (24311/100000 : ℝ) ^ (4743/1024 : ℝ) ≤ (35733820626106811/25000000000000000000 : ℝ) := by
    have hpowers : (24311/100000 : ℝ)^4743 ≤ (35733820626106811/25000000000000000000 : ℝ)^1024 := by
      have hnat : (24311 : ℕ)^4743*25000000000000000000^1024 ≤ 35733820626106811^1024*100000^4743 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        24311 100000 35733820626106811 25000000000000000000 4743 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (24311/100000 : ℝ)) (X := (35733820626106811/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4743 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (2500001592940920327/2500000000000000000 : ℝ) ≤ (10000001375645031/10000000000000000 : ℝ) ^ (4743/1024 : ℝ) := by
    have hpowers : (2500001592940920327/2500000000000000000 : ℝ)^1024 ≤ (10000001375645031/10000000000000000 : ℝ)^4743 := by
      have hnat : (2500001592940920327 : ℕ)^1024*10000000000000000^4743 ≤ 10000001375645031^4743*2500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2500001592940920327 2500000000000000000 10000001375645031 10000000000000000 1024 4743 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000001375645031/10000000000000000 : ℝ)) (X := (2500001592940920327/2500000000000000000 : ℝ)) (by norm_num) 4743 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (12517870892665354223/12500000000000000000 : ℝ) ≤ (10003084890690309/10000000000000000 : ℝ) ^ (4743/1024 : ℝ) := by
    have hpowers : (12517870892665354223/12500000000000000000 : ℝ)^1024 ≤ (10003084890690309/10000000000000000 : ℝ)^4743 := by
      have hnat : (12517870892665354223 : ℕ)^1024*10000000000000000^4743 ≤ 10003084890690309^4743*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12517870892665354223 12500000000000000000 10003084890690309 10000000000000000 1024 4743 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003084890690309/10000000000000000 : ℝ)) (X := (12517870892665354223/12500000000000000000 : ℝ)) (by norm_num) 4743 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12535733820626106811/12500000000000000000 : ℝ) ≤ (10006168405735587/10000000000000000 : ℝ) ^ (4743/1024 : ℝ) := by
    have hpowers : (12535733820626106811/12500000000000000000 : ℝ)^1024 ≤ (10006168405735587/10000000000000000 : ℝ)^4743 := by
      have hnat : (12535733820626106811 : ℕ)^1024*10000000000000000^4743 ≤ 10006168405735587^4743*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12535733820626106811 12500000000000000000 10006168405735587 10000000000000000 1024 4743 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10006168405735587/10000000000000000 : ℝ)) (X := (12535733820626106811/12500000000000000000 : ℝ)) (by norm_num) 4743 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1592940920327/5000000000000000000 : ℝ) ≤ ((101757812530905315441/101770000000000000000 : ℝ)+2*(1541757522639/1017700000000000 : ℝ)*(3957/100000 : ℝ))^(4743/1024 : ℝ) := by
    rw [show (101757812530905315441/101770000000000000000 : ℝ)+2*(1541757522639/1017700000000000 : ℝ)*(3957/100000 : ℝ)=(10000001375645031/10000000000000000 : ℝ) by norm_num, show 1+2*(1592940920327/5000000000000000000 : ℝ)=(2500001592940920327/2500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(35733820626106811/25000000000000000000 : ℝ)+(1592940920327/5000000000000000000 : ℝ) ≤ ((101757812530905315441/101770000000000000000 : ℝ)+(1541757522639/1017700000000000 : ℝ)*((24311/100000 : ℝ)+(3957/100000 : ℝ)))^(4743/1024 : ℝ) := by
    rw [show (101757812530905315441/101770000000000000000 : ℝ)+(1541757522639/1017700000000000 : ℝ)*((24311/100000 : ℝ)+(3957/100000 : ℝ))=(10003084890690309/10000000000000000 : ℝ) by norm_num, show 1+(35733820626106811/25000000000000000000 : ℝ)+(1592940920327/5000000000000000000 : ℝ)=(12517870892665354223/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(35733820626106811/25000000000000000000 : ℝ) ≤ ((101757812530905315441/101770000000000000000 : ℝ)+2*(1541757522639/1017700000000000 : ℝ)*(24311/100000 : ℝ))^(4743/1024 : ℝ) := by
    rw [show (101757812530905315441/101770000000000000000 : ℝ)+2*(1541757522639/1017700000000000 : ℝ)*(24311/100000 : ℝ)=(10006168405735587/10000000000000000 : ℝ) by norm_num, show 1+2*(35733820626106811/25000000000000000000 : ℝ)=(12535733820626106811/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (101757812530905315441/101770000000000000000 : ℝ)*(X 1 0+X 2 0)+(1541757522639/1017700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4743/1024 : ℝ)) (lo := (3957/100000 : ℝ)) (hi := (24311/100000 : ℝ)) (c := (101757812530905315441/101770000000000000000 : ℝ)) (alpha := (1541757522639/1017700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (101757812530905315441/101770000000000000000 : ℝ)*(X 0 1+X 2 1)+(1541757522639/1017700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4743/1024 : ℝ)) (lo := (3957/100000 : ℝ)) (hi := (24311/100000 : ℝ)) (c := (101757812530905315441/101770000000000000000 : ℝ)) (alpha := (1541757522639/1017700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (101757812530905315441/101770000000000000000 : ℝ)*(X 0 2+X 1 2)+(1541757522639/1017700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4743/1024 : ℝ)) (lo := (3957/100000 : ℝ)) (hi := (24311/100000 : ℝ)) (c := (101757812530905315441/101770000000000000000 : ℝ)) (alpha := (1541757522639/1017700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1696010069/10000000000 : ℝ)*X 0 0+(5532733783/10000000000 : ℝ)*X 0 1+(5118530827/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1607_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5372861907/10000000000 : ℝ)*X 1 0+(-1912742749/10000000000 : ℝ)*X 1 1+(1023706137/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1607_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5372861567/10000000000 : ℝ)*X 2 0+(5118530969/10000000000 : ℝ)*X 2 1+(-1912742827/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1607_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((525430833/1250000000 : ℝ)*X 0 0+(3720111503/10000000000 : ℝ)*X 0 1+(473393011/1000000000 : ℝ)*X 0 2+(525430833/1250000000 : ℝ)*X 1 0+(3720111503/10000000000 : ℝ)*X 1 1+(473393011/1000000000 : ℝ)*X 1 2+(525430833/1250000000 : ℝ)*X 2 0+(3720111503/10000000000 : ℝ)*X 2 1+(473393011/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1607_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1696239229/10000000000 : ℝ)*X 0 0+(5123064141/10000000000 : ℝ)*X 0 1+(2764064927/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1607_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((263136179/500000000 : ℝ)*X 1 0+(-1503143351/10000000000 : ℝ)*X 1 1+(221125207/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1607_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2631361479/5000000000 : ℝ)*X 2 0+(5528130409/10000000000 : ℝ)*X 2 1+(-1503143893/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1607_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((168160259/400000000 : ℝ)*X 0 0+(2361417669/5000000000 : ℝ)*X 0 1+(932844793/2500000000 : ℝ)*X 0 2+(168160259/400000000 : ℝ)*X 1 0+(2361417669/5000000000 : ℝ)*X 1 1+(932844793/2500000000 : ℝ)*X 1 2+(168160259/400000000 : ℝ)*X 2 0+(2361417669/5000000000 : ℝ)*X 2 1+(932844793/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1607_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (12931336845017132932690223877/1272125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (71511047/50000000000000 : ℝ)*(base1) + (2078595993/100000000000000 : ℝ)*(base19) + (1925816333/100000000000000 : ℝ)*(base23) + (264838337/100000000000000 : ℝ)*(upper3) + (755489/390625000000 : ℝ)*(upper5) + (425086440167399/25000000000000 : ℝ)*(major0) + (425086440167399/25000000000000 : ℝ)*(major1) + (425086440167399/25000000000000 : ℝ)*(major2) + (603573074475061/25000000000000 : ℝ)*(sp0) + (1207152879131967/50000000000000 : ℝ)*(sp1) + (1207152955521797/50000000000000 : ℝ)*(sp2) + (197275256350907/20000000000000 : ℝ)*(sp3) + (15681981777/100000000000000 : ℝ)*(sp4) + (6920864419/100000000000000 : ℝ)*(sp7) + (986383345641047/100000000000000 : ℝ)*(f.failure) + (2414307836859927/100000000000000 : ℝ)*(f.sum) + (31250370962529/12721250000000000000000000000 : ℝ)*base66 + (2862169294332392041/2544250000000000000000000000000000 : ℝ)*base68 + (13741295606646392041/2544250000000000000000000000000000 : ℝ)*base70 + (14784392340202857959/2544250000000000000000000000000000 : ℝ)*base71 + (193980816608641/50885000000000000000000000000 : ℝ)*base74 + (16044662234793392041/2544250000000000000000000000000000 : ℝ)*base76 + (476574347747857959/2544250000000000000000000000000000 : ℝ)*base77 + (11744555610064642041/2544250000000000000000000000000000 : ℝ)*base80 + (73950292070739/12721250000000000000000000000 : ℝ)*base82 + (767331/125000000000000000000 : ℝ)*base89 + (767331/125000000000000000000 : ℝ)*base91 + (767331/125000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (8851243056300557596961710449/5088500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (508073167/100000000000000 : ℝ)*(base19) + (325815901/100000000000000 : ℝ)*(base23) + (72584857/100000000000000 : ℝ)*(upper2) + (120768741/100000000000000 : ℝ)*(upper3) + (1738674968257237/100000000000000 : ℝ)*(major0) + (1738674968257237/100000000000000 : ℝ)*(major1) + (1738674968257237/100000000000000 : ℝ)*(major2) + (35415931/781250000000 : ℝ)*(sp1) + (635228609/20000000000000 : ℝ)*(sp2) + (392485119/100000000000000 : ℝ)*(sp3) + (38573929245487/1562500000000 : ℝ)*(sp4) + (2468726430398833/100000000000000 : ℝ)*(sp5) + (1234363984876111/50000000000000 : ℝ)*(sp6) + (504309007168089/50000000000000 : ℝ)*(sp7) + (1008618406821297/100000000000000 : ℝ)*(f.failure) + (38573929245487/1562500000000 : ℝ)*(f.sum) + (246196095054747/50885000000000000000000000000 : ℝ)*base66 + (40648280848867396517/10177000000000000000000000000000000 : ℝ)*base67 + (17937099689854396517/10177000000000000000000000000000000 : ℝ)*base69 + (30884544668846396517/10177000000000000000000000000000000 : ℝ)*base71 + (118558385339867/50885000000000000000000000000 : ℝ)*base74 + (38626120649936603483/10177000000000000000000000000000000 : ℝ)*base76 + (48135877816628603483/10177000000000000000000000000000000 : ℝ)*base78 + (63547012068312396517/10177000000000000000000000000000000 : ℝ)*base79 + (26142234378309/25442500000000000000000000000 : ℝ)*base81 + (350581/125000000000000000000 : ℝ)*base89 + (350581/125000000000000000000 : ℝ)*base91 + (350581/125000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1607_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4743/1024 : ℝ) ≤ p) (hpb : p ≤ (4747/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (2154773/1250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (24311/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3957/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2269/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4463/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1607_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1607_s2_0 (p : ℝ) (hpa : (4743/1024 : ℝ) ≤ p) (hpb : p ≤ (4747/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-85516633/500000000 : ℝ)*x 0 + (546803147/1000000000 : ℝ)*x 1 + (5173861917/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (85516633/500000000 : ℝ)^4747 ≤ (5261525822081/50000000000000 : ℝ)^3723 := by
    have hnat : (85516633 : ℕ)^4747*50000000000000^3723 ≤ 5261525822081^3723*500000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      85516633 500000000 5261525822081 50000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (546803147/1000000000 : ℝ)^4747 ≤ (11578764402259/25000000000000 : ℝ)^3723 := by
    have hnat : (546803147 : ℕ)^4747*25000000000000^3723 ≤ 11578764402259^3723*1000000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      546803147 1000000000 11578764402259 25000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5173861917/10000000000 : ℝ)^4747 ≤ (21580945367141/50000000000000 : ℝ)^3723 := by
    have hnat : (5173861917 : ℕ)^4747*50000000000000^3723 ≤ 21580945367141^3723*10000000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5173861917 10000000000 21580945367141 50000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4747/1024 : ℝ)) 4747 3723 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-85516633/500000000 : ℝ), (546803147/1000000000 : ℝ), (5173861917/10000000000 : ℝ)] ![(5261525822081/50000000000000 : ℝ), (11578764402259/25000000000000 : ℝ), (21580945367141/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-85516633/500000000 : ℝ)|^4747 ≤ (5261525822081/50000000000000 : ℝ)^3723
        have hw : |(-85516633/500000000 : ℝ)|=(85516633/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(546803147/1000000000 : ℝ)|^4747 ≤ (11578764402259/25000000000000 : ℝ)^3723
        have hw : |(546803147/1000000000 : ℝ)|=(546803147/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5173861917/10000000000 : ℝ)|^4747 ≤ (21580945367141/50000000000000 : ℝ)^3723
        have hw : |(5173861917/10000000000 : ℝ)|=(5173861917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1607_s2_1 (p : ℝ) (hpa : (4743/1024 : ℝ) ≤ p) (hpb : p ≤ (4747/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (41843933/78125000 : ℝ)*x 0 + (-1862276521/10000000000 : ℝ)*x 1 + (1034772357/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (41843933/78125000 : ℝ)^4747 ≤ (45108813140413/100000000000000 : ℝ)^3723 := by
    have hnat : (41843933 : ℕ)^4747*100000000000000^3723 ≤ 45108813140413^3723*78125000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41843933 78125000 45108813140413 100000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1862276521/10000000000 : ℝ)^4747 ≤ (11729297515219/100000000000000 : ℝ)^3723 := by
    have hnat : (1862276521 : ℕ)^4747*100000000000000^3723 ≤ 11729297515219^3723*10000000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1862276521 10000000000 11729297515219 100000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1034772357/2000000000 : ℝ)^4747 ≤ (43161889330221/100000000000000 : ℝ)^3723 := by
    have hnat : (1034772357 : ℕ)^4747*100000000000000^3723 ≤ 43161889330221^3723*2000000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1034772357 2000000000 43161889330221 100000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4747/1024 : ℝ)) 4747 3723 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(41843933/78125000 : ℝ), (-1862276521/10000000000 : ℝ), (1034772357/2000000000 : ℝ)] ![(45108813140413/100000000000000 : ℝ), (11729297515219/100000000000000 : ℝ), (43161889330221/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(41843933/78125000 : ℝ)|^4747 ≤ (45108813140413/100000000000000 : ℝ)^3723
        have hw : |(41843933/78125000 : ℝ)|=(41843933/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1862276521/10000000000 : ℝ)|^4747 ≤ (11729297515219/100000000000000 : ℝ)^3723
        have hw : |(-1862276521/10000000000 : ℝ)|=(1862276521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1034772357/2000000000 : ℝ)|^4747 ≤ (43161889330221/100000000000000 : ℝ)^3723
        have hw : |(1034772357/2000000000 : ℝ)|=(1034772357/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1607_s2_2 (p : ℝ) (hpa : (4743/1024 : ℝ) ≤ p) (hpb : p ≤ (4747/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (53560233/100000000 : ℝ)*x 0 + (2586930961/5000000000 : ℝ)*x 1 + (-372455301/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (53560233/100000000 : ℝ)^4747 ≤ (22554405904417/50000000000000 : ℝ)^3723 := by
    have hnat : (53560233 : ℕ)^4747*50000000000000^3723 ≤ 22554405904417^3723*100000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53560233 100000000 22554405904417 50000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2586930961/5000000000 : ℝ)^4747 ≤ (21580945393733/50000000000000 : ℝ)^3723 := by
    have hnat : (2586930961 : ℕ)^4747*50000000000000^3723 ≤ 21580945393733^3723*5000000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2586930961 5000000000 21580945393733 50000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (372455301/2000000000 : ℝ)^4747 ≤ (1466162173341/12500000000000 : ℝ)^3723 := by
    have hnat : (372455301 : ℕ)^4747*12500000000000^3723 ≤ 1466162173341^3723*2000000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      372455301 2000000000 1466162173341 12500000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4747/1024 : ℝ)) 4747 3723 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(53560233/100000000 : ℝ), (2586930961/5000000000 : ℝ), (-372455301/2000000000 : ℝ)] ![(22554405904417/50000000000000 : ℝ), (21580945393733/50000000000000 : ℝ), (1466162173341/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(53560233/100000000 : ℝ)|^4747 ≤ (22554405904417/50000000000000 : ℝ)^3723
        have hw : |(53560233/100000000 : ℝ)|=(53560233/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2586930961/5000000000 : ℝ)|^4747 ≤ (21580945393733/50000000000000 : ℝ)^3723
        have hw : |(2586930961/5000000000 : ℝ)|=(2586930961/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-372455301/2000000000 : ℝ)|^4747 ≤ (1466162173341/12500000000000 : ℝ)^3723
        have hw : |(-372455301/2000000000 : ℝ)|=(372455301/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1607_s2_3 (p : ℝ) (hpa : (4743/1024 : ℝ) ≤ p) (hpb : p ≤ (4747/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4214005827/10000000000 : ℝ)*x 0 + (1932944629/5000000000 : ℝ)*x 1 + (1146477339/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4214005827/10000000000 : ℝ)^4747 ≤ (16612640085503/50000000000000 : ℝ)^3723 := by
    have hnat : (4214005827 : ℕ)^4747*50000000000000^3723 ≤ 16612640085503^3723*10000000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4214005827 10000000000 16612640085503 50000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1932944629/5000000000 : ℝ)^4747 ≤ (3720776711353/12500000000000 : ℝ)^3723 := by
    have hnat : (1932944629 : ℕ)^4747*12500000000000^3723 ≤ 3720776711353^3723*5000000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1932944629 5000000000 3720776711353 12500000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1146477339/2500000000 : ℝ)^4747 ≤ (9252126530897/25000000000000 : ℝ)^3723 := by
    have hnat : (1146477339 : ℕ)^4747*25000000000000^3723 ≤ 9252126530897^3723*2500000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1146477339 2500000000 9252126530897 25000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4747/1024 : ℝ)) 4747 3723 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4214005827/10000000000 : ℝ), (1932944629/5000000000 : ℝ), (1146477339/2500000000 : ℝ)] ![(16612640085503/50000000000000 : ℝ), (3720776711353/12500000000000 : ℝ), (9252126530897/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4214005827/10000000000 : ℝ)|^4747 ≤ (16612640085503/50000000000000 : ℝ)^3723
        have hw : |(4214005827/10000000000 : ℝ)|=(4214005827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1932944629/5000000000 : ℝ)|^4747 ≤ (3720776711353/12500000000000 : ℝ)^3723
        have hw : |(1932944629/5000000000 : ℝ)|=(1932944629/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1146477339/2500000000 : ℝ)|^4747 ≤ (9252126530897/25000000000000 : ℝ)^3723
        have hw : |(1146477339/2500000000 : ℝ)|=(1146477339/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1607_s2_4 (p : ℝ) (hpa : (4743/1024 : ℝ) ≤ p) (hpb : p ≤ (4747/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-855207293/5000000000 : ℝ)*x 0 + (5176155847/10000000000 : ℝ)*x 1 + (5465712383/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (855207293/5000000000 : ℝ)^4747 ≤ (131546179369/1250000000000 : ℝ)^3723 := by
    have hnat : (855207293 : ℕ)^4747*1250000000000^3723 ≤ 131546179369^3723*5000000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      855207293 5000000000 131546179369 1250000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5176155847/10000000000 : ℝ)^4747 ≤ (43186292343099/100000000000000 : ℝ)^3723 := by
    have hnat : (5176155847 : ℕ)^4747*100000000000000^3723 ≤ 43186292343099^3723*10000000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5176155847 10000000000 43186292343099 100000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5465712383/10000000000 : ℝ)^4747 ≤ (46290013297007/100000000000000 : ℝ)^3723 := by
    have hnat : (5465712383 : ℕ)^4747*100000000000000^3723 ≤ 46290013297007^3723*10000000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5465712383 10000000000 46290013297007 100000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4747/1024 : ℝ)) 4747 3723 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-855207293/5000000000 : ℝ), (5176155847/10000000000 : ℝ), (5465712383/10000000000 : ℝ)] ![(131546179369/1250000000000 : ℝ), (43186292343099/100000000000000 : ℝ), (46290013297007/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-855207293/5000000000 : ℝ)|^4747 ≤ (131546179369/1250000000000 : ℝ)^3723
        have hw : |(-855207293/5000000000 : ℝ)|=(855207293/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5176155847/10000000000 : ℝ)|^4747 ≤ (43186292343099/100000000000000 : ℝ)^3723
        have hw : |(5176155847/10000000000 : ℝ)|=(5176155847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5465712383/10000000000 : ℝ)|^4747 ≤ (46290013297007/100000000000000 : ℝ)^3723
        have hw : |(5465712383/10000000000 : ℝ)|=(5465712383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1607_s2_5 (p : ℝ) (hpa : (4743/1024 : ℝ) ≤ p) (hpb : p ≤ (4747/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5277929463/10000000000 : ℝ)*x 0 + (-314085219/2000000000 : ℝ)*x 1 + (5465712567/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5277929463/10000000000 : ℝ)^4747 ≤ (8854377152227/20000000000000 : ℝ)^3723 := by
    have hnat : (5277929463 : ℕ)^4747*20000000000000^3723 ≤ 8854377152227^3723*10000000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5277929463 10000000000 8854377152227 20000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (314085219/2000000000 : ℝ)^4747 ≤ (9438098927537/100000000000000 : ℝ)^3723 := by
    have hnat : (314085219 : ℕ)^4747*100000000000000^3723 ≤ 9438098927537^3723*2000000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      314085219 2000000000 9438098927537 100000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5465712567/10000000000 : ℝ)^4747 ≤ (23145007641973/50000000000000 : ℝ)^3723 := by
    have hnat : (5465712567 : ℕ)^4747*50000000000000^3723 ≤ 23145007641973^3723*10000000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5465712567 10000000000 23145007641973 50000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4747/1024 : ℝ)) 4747 3723 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5277929463/10000000000 : ℝ), (-314085219/2000000000 : ℝ), (5465712567/10000000000 : ℝ)] ![(8854377152227/20000000000000 : ℝ), (9438098927537/100000000000000 : ℝ), (23145007641973/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5277929463/10000000000 : ℝ)|^4747 ≤ (8854377152227/20000000000000 : ℝ)^3723
        have hw : |(5277929463/10000000000 : ℝ)|=(5277929463/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-314085219/2000000000 : ℝ)|^4747 ≤ (9438098927537/100000000000000 : ℝ)^3723
        have hw : |(-314085219/2000000000 : ℝ)|=(314085219/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5465712567/10000000000 : ℝ)|^4747 ≤ (23145007641973/50000000000000 : ℝ)^3723
        have hw : |(5465712567/10000000000 : ℝ)|=(5465712567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1607_s2_6 (p : ℝ) (hpa : (4743/1024 : ℝ) ≤ p) (hpb : p ≤ (4747/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (659741233/1250000000 : ℝ)*x 0 + (5465711973/10000000000 : ℝ)*x 1 + (-12563411/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (659741233/1250000000 : ℝ)^4747 ≤ (44271890049927/100000000000000 : ℝ)^3723 := by
    have hnat : (659741233 : ℕ)^4747*100000000000000^3723 ≤ 44271890049927^3723*1250000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      659741233 1250000000 44271890049927 100000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5465711973/10000000000 : ℝ)^4747 ≤ (11572502217397/25000000000000 : ℝ)^3723 := by
    have hnat : (5465711973 : ℕ)^4747*25000000000000^3723 ≤ 11572502217397^3723*10000000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5465711973 10000000000 11572502217397 25000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (12563411/80000000 : ℝ)^4747 ≤ (188762021463/2000000000000 : ℝ)^3723 := by
    have hnat : (12563411 : ℕ)^4747*2000000000000^3723 ≤ 188762021463^3723*80000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      12563411 80000000 188762021463 2000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4747/1024 : ℝ)) 4747 3723 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(659741233/1250000000 : ℝ), (5465711973/10000000000 : ℝ), (-12563411/80000000 : ℝ)] ![(44271890049927/100000000000000 : ℝ), (11572502217397/25000000000000 : ℝ), (188762021463/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(659741233/1250000000 : ℝ)|^4747 ≤ (44271890049927/100000000000000 : ℝ)^3723
        have hw : |(659741233/1250000000 : ℝ)|=(659741233/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5465711973/10000000000 : ℝ)|^4747 ≤ (11572502217397/25000000000000 : ℝ)^3723
        have hw : |(5465711973/10000000000 : ℝ)|=(5465711973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-12563411/80000000 : ℝ)|^4747 ≤ (188762021463/2000000000000 : ℝ)^3723
        have hw : |(-12563411/80000000 : ℝ)|=(12563411/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1607_s2_7 (p : ℝ) (hpa : (4743/1024 : ℝ) ≤ p) (hpb : p ≤ (4747/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4214206879/10000000000 : ℝ)*x 0 + (1145073699/2500000000 : ℝ)*x 1 + (967891463/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4214206879/10000000000 : ℝ)^4747 ≤ (33227301378793/100000000000000 : ℝ)^3723 := by
    have hnat : (4214206879 : ℕ)^4747*100000000000000^3723 ≤ 33227301378793^3723*10000000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4214206879 10000000000 33227301378793 100000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1145073699/2500000000 : ℝ)^4747 ≤ (18475371886317/50000000000000 : ℝ)^3723 := by
    have hnat : (1145073699 : ℕ)^4747*50000000000000^3723 ≤ 18475371886317^3723*2500000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1145073699 2500000000 18475371886317 50000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (967891463/2500000000 : ℝ)^4747 ≤ (5964390966909/20000000000000 : ℝ)^3723 := by
    have hnat : (967891463 : ℕ)^4747*20000000000000^3723 ≤ 5964390966909^3723*2500000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      967891463 2500000000 5964390966909 20000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4747/1024 : ℝ)) 4747 3723 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4214206879/10000000000 : ℝ), (1145073699/2500000000 : ℝ), (967891463/2500000000 : ℝ)] ![(33227301378793/100000000000000 : ℝ), (18475371886317/50000000000000 : ℝ), (5964390966909/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4214206879/10000000000 : ℝ)|^4747 ≤ (33227301378793/100000000000000 : ℝ)^3723
        have hw : |(4214206879/10000000000 : ℝ)|=(4214206879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1145073699/2500000000 : ℝ)|^4747 ≤ (18475371886317/50000000000000 : ℝ)^3723
        have hw : |(1145073699/2500000000 : ℝ)|=(1145073699/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(967891463/2500000000 : ℝ)|^4747 ≤ (5964390966909/20000000000000 : ℝ)^3723
        have hw : |(967891463/2500000000 : ℝ)|=(967891463/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1607_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4743/1024 : ℝ) ≤ p) (hpb : p ≤ (4747/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (2154773/1250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4463/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2269/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (10271/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16507/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4463/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2269/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4463/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2269/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4463/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2269/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4463/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2269/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4463/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2269/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4463/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2269/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2269/25000 : ℝ) ^ (4743/1024 : ℝ) ≤ (1489835214300647/100000000000000000000 : ℝ) := by
    have hpowers : (2269/25000 : ℝ)^4743 ≤ (1489835214300647/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2269 : ℕ)^4743*100000000000000000000^1024 ≤ 1489835214300647^1024*25000^4743 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2269 25000 1489835214300647 100000000000000000000 4743 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2269/25000 : ℝ)) (X := (1489835214300647/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4743 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (4463/25000 : ℝ) ^ (4743/1024 : ℝ) ≤ (17096467858498701/50000000000000000000 : ℝ) := by
    have hpowers : (4463/25000 : ℝ)^4743 ≤ (17096467858498701/50000000000000000000 : ℝ)^1024 := by
      have hnat : (4463 : ℕ)^4743*50000000000000000000^1024 ≤ 17096467858498701^1024*25000^4743 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4463 25000 17096467858498701 50000000000000000000 4743 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4463/25000 : ℝ)) (X := (17096467858498701/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4743 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001489835214300647/50000000000000000000 : ℝ) ≤ (2500016082368101/2500000000000000 : ℝ) ^ (4743/1024 : ℝ) := by
    have hpowers : (50001489835214300647/50000000000000000000 : ℝ)^1024 ≤ (2500016082368101/2500000000000000 : ℝ)^4743 := by
      have hnat : (50001489835214300647 : ℕ)^1024*2500000000000000^4743 ≤ 2500016082368101^4743*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001489835214300647 50000000000000000000 2500016082368101 2500000000000000 1024 4743 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500016082368101/2500000000000000 : ℝ)) (X := (50001489835214300647/50000000000000000000 : ℝ)) (by norm_num) 4743 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100035682770931298049/100000000000000000000 : ℝ) ≤ (10000770272968149/10000000000000000 : ℝ) ^ (4743/1024 : ℝ) := by
    have hpowers : (100035682770931298049/100000000000000000000 : ℝ)^1024 ≤ (10000770272968149/10000000000000000 : ℝ)^4743 := by
      have hnat : (100035682770931298049 : ℕ)^1024*10000000000000000^4743 ≤ 10000770272968149^4743*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100035682770931298049 100000000000000000000 10000770272968149 10000000000000000 1024 4743 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000770272968149/10000000000000000 : ℝ)) (X := (100035682770931298049/100000000000000000000 : ℝ)) (by norm_num) 4743 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25017096467858498701/25000000000000000000 : ℝ) ≤ (5000738108231947/5000000000000000 : ℝ) ^ (4743/1024 : ℝ) := by
    have hpowers : (25017096467858498701/25000000000000000000 : ℝ)^1024 ≤ (5000738108231947/5000000000000000 : ℝ)^4743 := by
      have hnat : (25017096467858498701 : ℕ)^1024*5000000000000000^4743 ≤ 5000738108231947^4743*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25017096467858498701 25000000000000000000 5000738108231947 5000000000000000 1024 4743 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000738108231947/5000000000000000 : ℝ)) (X := (25017096467858498701/25000000000000000000 : ℝ)) (by norm_num) 4743 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1489835214300647/100000000000000000000 : ℝ) ≤ ((10968468783639381783/10970000000000000000 : ℝ)+2*(141188699149/175520000000000 : ℝ)*(2269/25000 : ℝ))^(4743/1024 : ℝ) := by
    rw [show (10968468783639381783/10970000000000000000 : ℝ)+2*(141188699149/175520000000000 : ℝ)*(2269/25000 : ℝ)=(2500016082368101/2500000000000000 : ℝ) by norm_num, show 1+2*(1489835214300647/100000000000000000000 : ℝ)=(50001489835214300647/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(17096467858498701/50000000000000000000 : ℝ)+(1489835214300647/100000000000000000000 : ℝ) ≤ ((10968468783639381783/10970000000000000000 : ℝ)+(141188699149/175520000000000 : ℝ)*((4463/25000 : ℝ)+(2269/25000 : ℝ)))^(4743/1024 : ℝ) := by
    rw [show (10968468783639381783/10970000000000000000 : ℝ)+(141188699149/175520000000000 : ℝ)*((4463/25000 : ℝ)+(2269/25000 : ℝ))=(10000770272968149/10000000000000000 : ℝ) by norm_num, show 1+(17096467858498701/50000000000000000000 : ℝ)+(1489835214300647/100000000000000000000 : ℝ)=(100035682770931298049/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(17096467858498701/50000000000000000000 : ℝ) ≤ ((10968468783639381783/10970000000000000000 : ℝ)+2*(141188699149/175520000000000 : ℝ)*(4463/25000 : ℝ))^(4743/1024 : ℝ) := by
    rw [show (10968468783639381783/10970000000000000000 : ℝ)+2*(141188699149/175520000000000 : ℝ)*(4463/25000 : ℝ)=(5000738108231947/5000000000000000 : ℝ) by norm_num, show 1+2*(17096467858498701/50000000000000000000 : ℝ)=(25017096467858498701/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (10968468783639381783/10970000000000000000 : ℝ)*(X 1 0+X 2 0)+(141188699149/175520000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4743/1024 : ℝ)) (lo := (2269/25000 : ℝ)) (hi := (4463/25000 : ℝ)) (c := (10968468783639381783/10970000000000000000 : ℝ)) (alpha := (141188699149/175520000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (10968468783639381783/10970000000000000000 : ℝ)*(X 0 1+X 2 1)+(141188699149/175520000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4743/1024 : ℝ)) (lo := (2269/25000 : ℝ)) (hi := (4463/25000 : ℝ)) (c := (10968468783639381783/10970000000000000000 : ℝ)) (alpha := (141188699149/175520000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (10968468783639381783/10970000000000000000 : ℝ)*(X 0 2+X 1 2)+(141188699149/175520000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4743/1024 : ℝ)) (lo := (2269/25000 : ℝ)) (hi := (4463/25000 : ℝ)) (c := (10968468783639381783/10970000000000000000 : ℝ)) (alpha := (141188699149/175520000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-85516633/500000000 : ℝ)*X 0 0+(546803147/1000000000 : ℝ)*X 0 1+(5173861917/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1607_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((41843933/78125000 : ℝ)*X 1 0+(-1862276521/10000000000 : ℝ)*X 1 1+(1034772357/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1607_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((53560233/100000000 : ℝ)*X 2 0+(2586930961/5000000000 : ℝ)*X 2 1+(-372455301/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1607_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4214005827/10000000000 : ℝ)*X 0 0+(1932944629/5000000000 : ℝ)*X 0 1+(1146477339/2500000000 : ℝ)*X 0 2+(4214005827/10000000000 : ℝ)*X 1 0+(1932944629/5000000000 : ℝ)*X 1 1+(1146477339/2500000000 : ℝ)*X 1 2+(4214005827/10000000000 : ℝ)*X 2 0+(1932944629/5000000000 : ℝ)*X 2 1+(1146477339/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1607_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-855207293/5000000000 : ℝ)*X 0 0+(5176155847/10000000000 : ℝ)*X 0 1+(5465712383/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1607_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5277929463/10000000000 : ℝ)*X 1 0+(-314085219/2000000000 : ℝ)*X 1 1+(5465712567/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1607_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((659741233/1250000000 : ℝ)*X 2 0+(5465711973/10000000000 : ℝ)*X 2 1+(-12563411/80000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1607_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4214206879/10000000000 : ℝ)*X 0 0+(1145073699/2500000000 : ℝ)*X 0 1+(967891463/2500000000 : ℝ)*X 0 2+(4214206879/10000000000 : ℝ)*X 1 0+(1145073699/2500000000 : ℝ)*X 1 1+(967891463/2500000000 : ℝ)*X 1 2+(4214206879/10000000000 : ℝ)*X 2 0+(1145073699/2500000000 : ℝ)*X 2 1+(967891463/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1607_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3065479386705295320557435859/274250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2041190793/100000000000000 : ℝ)*(base19) + (1896145261/100000000000000 : ℝ)*(base23) + (7106723/20000000000000 : ℝ)*(lower2) + (54572037/20000000000000 : ℝ)*(upper3) + (55501427/25000000000000 : ℝ)*(upper5) + (1197078925980991/50000000000000 : ℝ)*(major0) + (1197078925980991/50000000000000 : ℝ)*(major1) + (1197078925980991/50000000000000 : ℝ)*(major2) + (3399423513907101/100000000000000 : ℝ)*(sp0) + (849861084925239/25000000000000 : ℝ)*(sp1) + (424930560593311/12500000000000 : ℝ)*(sp2) + (86803703513031/6250000000000 : ℝ)*(sp3) + (2858373081/12500000000000 : ℝ)*(sp4) + (9694234301/100000000000000 : ℝ)*(sp7) + (1388868950442797/100000000000000 : ℝ)*(f.failure) + (849861595222937/25000000000000 : ℝ)*(f.sum) + (1792536682411/877600000000000000000000000 : ℝ)*base65 + (1284921534824125547/548500000000000000000000000000000 : ℝ)*base68 + (4018540189365625547/548500000000000000000000000000000 : ℝ)*base70 + (332405882736625547/548500000000000000000000000000000 : ℝ)*base72 + (2766399656663/877600000000000000000000000 : ℝ)*base73 + (154394244672874453/548500000000000000000000000000000 : ℝ)*base75 + (787648297952625547/548500000000000000000000000000000 : ℝ)*base78 + (1919676216590874453/548500000000000000000000000000000 : ℝ)*base79 + (661533890503/877600000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (479919/125000000000000000000 : ℝ)*base90 + (479919/125000000000000000000 : ℝ)*base92 + (479919/125000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3256272434614454672038897407/274250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1507209873/100000000000000 : ℝ)*(base19) + (984958909/50000000000000 : ℝ)*(base23) + (1616511/800000000000 : ℝ)*(upper3) + (2834801/2500000000000 : ℝ)*(lower4) + (58923977/25000000000000 : ℝ)*(upper5) + (1216133413420881/50000000000000 : ℝ)*(major0) + (1216133413420881/50000000000000 : ℝ)*(major1) + (1216133413420881/50000000000000 : ℝ)*(major2) + (18670289281/100000000000000 : ℝ)*(sp1) + (3537764099/20000000000000 : ℝ)*(sp2) + (3453557004929197/100000000000000 : ℝ)*(sp4) + (1726768413715021/50000000000000 : ℝ)*(sp5) + (863384336547721/25000000000000 : ℝ)*(sp6) + (705488126487617/50000000000000 : ℝ)*(sp7) + (705488126487617/50000000000000 : ℝ)*(f.failure) + (3453557004929197/100000000000000 : ℝ)*(f.sum) + (4289671936403/4388000000000000000000000000 : ℝ)*base66 + (4629263234300476677/548500000000000000000000000000000 : ℝ)*base68 + (4053343004056476677/548500000000000000000000000000000 : ℝ)*base70 + (3227863918720976677/548500000000000000000000000000000 : ℝ)*base72 + (3390422626491/877600000000000000000000000 : ℝ)*base74 + (23303948534476677/548500000000000000000000000000000 : ℝ)*base76 + (7018244474491976677/548500000000000000000000000000000 : ℝ)*base78 + (1296237527955976677/548500000000000000000000000000000 : ℝ)*base80 + (1385556417557/877600000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (695941/62500000000000000000 : ℝ)*base89 + (695941/62500000000000000000 : ℝ)*base91 + (695941/62500000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1607_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4743/1024 : ℝ) ≤ p) (hpb : p ≤ (4747/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (2154773/1250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4463/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2269/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10271/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16507/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1607_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1607_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4743/1024 : ℝ) ≤ p) (hpb : p ≤ (4747/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (2154773/1250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10271/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16507/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1607_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1607_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1607_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4743/1024 : ℝ) ≤ p) (hpb : p ≤ (4747/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (2154773/1250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10271/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16507/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1607_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
