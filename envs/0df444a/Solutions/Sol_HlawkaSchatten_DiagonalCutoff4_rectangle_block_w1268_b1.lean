-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1268_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:19:59.507812+00:00
-- url     : https://prove2.me/submissions/11ccf467-c82e-45ec-b27d-f94ac46ef508

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
theorem support_rectangle_w1268_s3_0 (p : ℝ) (hpa : (2115/512 : ℝ) ≤ p) (hpb : p ≤ (8461/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2105413831/10000000000 : ℝ)*x 0 + (5417426363/10000000000 : ℝ)*x 1 + (2621283413/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2105413831/10000000000 : ℝ)^8461 ≤ (2560202971009/20000000000000 : ℝ)^6413 := by
    have hnat : (2105413831 : ℕ)^8461*20000000000000^6413 ≤ 2560202971009^6413*10000000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2105413831 10000000000 2560202971009 20000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5417426363/10000000000 : ℝ)^8461 ≤ (11135750058891/25000000000000 : ℝ)^6413 := by
    have hnat : (5417426363 : ℕ)^8461*25000000000000^6413 ≤ 11135750058891^6413*10000000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5417426363 10000000000 11135750058891 25000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2621283413/5000000000 : ℝ)^8461 ≤ (21327992446879/50000000000000 : ℝ)^6413 := by
    have hnat : (2621283413 : ℕ)^8461*50000000000000^6413 ≤ 21327992446879^6413*5000000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621283413 5000000000 21327992446879 50000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8461/2048 : ℝ)) 8461 6413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2105413831/10000000000 : ℝ), (5417426363/10000000000 : ℝ), (2621283413/5000000000 : ℝ)] ![(2560202971009/20000000000000 : ℝ), (11135750058891/25000000000000 : ℝ), (21327992446879/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2105413831/10000000000 : ℝ)|^8461 ≤ (2560202971009/20000000000000 : ℝ)^6413
        have hw : |(-2105413831/10000000000 : ℝ)|=(2105413831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5417426363/10000000000 : ℝ)|^8461 ≤ (11135750058891/25000000000000 : ℝ)^6413
        have hw : |(5417426363/10000000000 : ℝ)|=(5417426363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2621283413/5000000000 : ℝ)|^8461 ≤ (21327992446879/50000000000000 : ℝ)^6413
        have hw : |(2621283413/5000000000 : ℝ)|=(2621283413/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1268_s3_1 (p : ℝ) (hpa : (2115/512 : ℝ) ≤ p) (hpb : p ≤ (8461/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5350921863/10000000000 : ℝ)*x 0 + (-2194575037/10000000000 : ℝ)*x 1 + (5242566951/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5350921863/10000000000 : ℝ)^8461 ≤ (2738936383203/6250000000000 : ℝ)^6413 := by
    have hnat : (5350921863 : ℕ)^8461*6250000000000^6413 ≤ 2738936383203^6413*10000000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5350921863 10000000000 2738936383203 6250000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2194575037/10000000000 : ℝ)^8461 ≤ (845064476123/6250000000000 : ℝ)^6413 := by
    have hnat : (2194575037 : ℕ)^8461*6250000000000^6413 ≤ 845064476123^6413*10000000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2194575037 10000000000 845064476123 6250000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5242566951/10000000000 : ℝ)^8461 ≤ (1332999569863/3125000000000 : ℝ)^6413 := by
    have hnat : (5242566951 : ℕ)^8461*3125000000000^6413 ≤ 1332999569863^6413*10000000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242566951 10000000000 1332999569863 3125000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8461/2048 : ℝ)) 8461 6413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5350921863/10000000000 : ℝ), (-2194575037/10000000000 : ℝ), (5242566951/10000000000 : ℝ)] ![(2738936383203/6250000000000 : ℝ), (845064476123/6250000000000 : ℝ), (1332999569863/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5350921863/10000000000 : ℝ)|^8461 ≤ (2738936383203/6250000000000 : ℝ)^6413
        have hw : |(5350921863/10000000000 : ℝ)|=(5350921863/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2194575037/10000000000 : ℝ)|^8461 ≤ (845064476123/6250000000000 : ℝ)^6413
        have hw : |(-2194575037/10000000000 : ℝ)|=(2194575037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5242566951/10000000000 : ℝ)|^8461 ≤ (1332999569863/3125000000000 : ℝ)^6413
        have hw : |(5242566951/10000000000 : ℝ)|=(5242566951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1268_s3_2 (p : ℝ) (hpa : (2115/512 : ℝ) ≤ p) (hpb : p ≤ (8461/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1337730463/2500000000 : ℝ)*x 0 + (20478779/39062500 : ℝ)*x 1 + (-2194574427/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337730463/2500000000 : ℝ)^8461 ≤ (4382298201239/10000000000000 : ℝ)^6413 := by
    have hnat : (1337730463 : ℕ)^8461*10000000000000^6413 ≤ 4382298201239^6413*2500000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337730463 2500000000 4382298201239 10000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (20478779/39062500 : ℝ)^8461 ≤ (21327995656603/50000000000000 : ℝ)^6413 := by
    have hnat : (20478779 : ℕ)^8461*50000000000000^6413 ≤ 21327995656603^6413*39062500^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20478779 39062500 21327995656603 50000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2194574427/10000000000 : ℝ)^8461 ≤ (3380256664869/25000000000000 : ℝ)^6413 := by
    have hnat : (2194574427 : ℕ)^8461*25000000000000^6413 ≤ 3380256664869^6413*10000000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2194574427 10000000000 3380256664869 25000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8461/2048 : ℝ)) 8461 6413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337730463/2500000000 : ℝ), (20478779/39062500 : ℝ), (-2194574427/10000000000 : ℝ)] ![(4382298201239/10000000000000 : ℝ), (21327995656603/50000000000000 : ℝ), (3380256664869/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337730463/2500000000 : ℝ)|^8461 ≤ (4382298201239/10000000000000 : ℝ)^6413
        have hw : |(1337730463/2500000000 : ℝ)|=(1337730463/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(20478779/39062500 : ℝ)|^8461 ≤ (21327995656603/50000000000000 : ℝ)^6413
        have hw : |(20478779/39062500 : ℝ)|=(20478779/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2194574427/10000000000 : ℝ)|^8461 ≤ (3380256664869/25000000000000 : ℝ)^6413
        have hw : |(-2194574427/10000000000 : ℝ)|=(2194574427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1268_s3_3 (p : ℝ) (hpa : (2115/512 : ℝ) ≤ p) (hpb : p ≤ (8461/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4345642459/10000000000 : ℝ)*x 0 + (2085462393/5000000000 : ℝ)*x 1 + (4527419457/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4345642459/10000000000 : ℝ)^8461 ≤ (2081354585601/6250000000000 : ℝ)^6413 := by
    have hnat : (4345642459 : ℕ)^8461*6250000000000^6413 ≤ 2081354585601^6413*10000000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4345642459 10000000000 2081354585601 6250000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2085462393/5000000000 : ℝ)^8461 ≤ (492916195247/1562500000000 : ℝ)^6413 := by
    have hnat : (2085462393 : ℕ)^8461*1562500000000^6413 ≤ 492916195247^6413*5000000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2085462393 5000000000 492916195247 1562500000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4527419457/10000000000 : ℝ)^8461 ≤ (1406067604699/4000000000000 : ℝ)^6413 := by
    have hnat : (4527419457 : ℕ)^8461*4000000000000^6413 ≤ 1406067604699^6413*10000000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4527419457 10000000000 1406067604699 4000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8461/2048 : ℝ)) 8461 6413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4345642459/10000000000 : ℝ), (2085462393/5000000000 : ℝ), (4527419457/10000000000 : ℝ)] ![(2081354585601/6250000000000 : ℝ), (492916195247/1562500000000 : ℝ), (1406067604699/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4345642459/10000000000 : ℝ)|^8461 ≤ (2081354585601/6250000000000 : ℝ)^6413
        have hw : |(4345642459/10000000000 : ℝ)|=(4345642459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2085462393/5000000000 : ℝ)|^8461 ≤ (492916195247/1562500000000 : ℝ)^6413
        have hw : |(2085462393/5000000000 : ℝ)|=(2085462393/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4527419457/10000000000 : ℝ)|^8461 ≤ (1406067604699/4000000000000 : ℝ)^6413
        have hw : |(4527419457/10000000000 : ℝ)|=(4527419457/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1268_s3_4 (p : ℝ) (hpa : (2115/512 : ℝ) ≤ p) (hpb : p ≤ (8461/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-263178459/1250000000 : ℝ)*x 0 + (1048638459/2000000000 : ℝ)*x 1 + (1083359431/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (263178459/1250000000 : ℝ)^8461 ≤ (12801125883759/100000000000000 : ℝ)^6413 := by
    have hnat : (263178459 : ℕ)^8461*100000000000000^6413 ≤ 12801125883759^6413*1250000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263178459 1250000000 12801125883759 100000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1048638459/2000000000 : ℝ)^8461 ≤ (21331349672441/50000000000000 : ℝ)^6413 := by
    have hnat : (1048638459 : ℕ)^8461*50000000000000^6413 ≤ 21331349672441^6413*2000000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048638459 2000000000 21331349672441 50000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1083359431/2000000000 : ℝ)^8461 ≤ (22268087378669/50000000000000 : ℝ)^6413 := by
    have hnat : (1083359431 : ℕ)^8461*50000000000000^6413 ≤ 22268087378669^6413*2000000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083359431 2000000000 22268087378669 50000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8461/2048 : ℝ)) 8461 6413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-263178459/1250000000 : ℝ), (1048638459/2000000000 : ℝ), (1083359431/2000000000 : ℝ)] ![(12801125883759/100000000000000 : ℝ), (21331349672441/50000000000000 : ℝ), (22268087378669/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-263178459/1250000000 : ℝ)|^8461 ≤ (12801125883759/100000000000000 : ℝ)^6413
        have hw : |(-263178459/1250000000 : ℝ)|=(263178459/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1048638459/2000000000 : ℝ)|^8461 ≤ (21331349672441/50000000000000 : ℝ)^6413
        have hw : |(1048638459/2000000000 : ℝ)|=(1048638459/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1083359431/2000000000 : ℝ)|^8461 ≤ (22268087378669/50000000000000 : ℝ)^6413
        have hw : |(1083359431/2000000000 : ℝ)|=(1083359431/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1268_s3_5 (p : ℝ) (hpa : (2115/512 : ℝ) ≤ p) (hpb : p ≤ (8461/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1061246967/2000000000 : ℝ)*x 0 + (-505086021/2500000000 : ℝ)*x 1 + (84637453/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1061246967/2000000000 : ℝ)^8461 ≤ (4334077389191/10000000000000 : ℝ)^6413 := by
    have hnat : (1061246967 : ℕ)^8461*10000000000000^6413 ≤ 4334077389191^6413*2000000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061246967 2000000000 4334077389191 10000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (505086021/2500000000 : ℝ)^8461 ≤ (12123053101991/100000000000000 : ℝ)^6413 := by
    have hnat : (505086021 : ℕ)^8461*100000000000000^6413 ≤ 12123053101991^6413*2500000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      505086021 2500000000 12123053101991 100000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (84637453/156250000 : ℝ)^8461 ≤ (44536172989191/100000000000000 : ℝ)^6413 := by
    have hnat : (84637453 : ℕ)^8461*100000000000000^6413 ≤ 44536172989191^6413*156250000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84637453 156250000 44536172989191 100000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8461/2048 : ℝ)) 8461 6413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1061246967/2000000000 : ℝ), (-505086021/2500000000 : ℝ), (84637453/156250000 : ℝ)] ![(4334077389191/10000000000000 : ℝ), (12123053101991/100000000000000 : ℝ), (44536172989191/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1061246967/2000000000 : ℝ)|^8461 ≤ (4334077389191/10000000000000 : ℝ)^6413
        have hw : |(1061246967/2000000000 : ℝ)|=(1061246967/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-505086021/2500000000 : ℝ)|^8461 ≤ (12123053101991/100000000000000 : ℝ)^6413
        have hw : |(-505086021/2500000000 : ℝ)|=(505086021/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(84637453/156250000 : ℝ)|^8461 ≤ (44536172989191/100000000000000 : ℝ)^6413
        have hw : |(84637453/156250000 : ℝ)|=(84637453/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1268_s3_6 (p : ℝ) (hpa : (2115/512 : ℝ) ≤ p) (hpb : p ≤ (8461/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5306234143/10000000000 : ℝ)*x 0 + (2708398717/5000000000 : ℝ)*x 1 + (-101017221/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5306234143/10000000000 : ℝ)^8461 ≤ (21670383217347/50000000000000 : ℝ)^6413 := by
    have hnat : (5306234143 : ℕ)^8461*50000000000000^6413 ≤ 21670383217347^6413*10000000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5306234143 10000000000 21670383217347 50000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2708398717/5000000000 : ℝ)^8461 ≤ (22268088891899/50000000000000 : ℝ)^6413 := by
    have hnat : (2708398717 : ℕ)^8461*50000000000000^6413 ≤ 22268088891899^6413*5000000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2708398717 5000000000 22268088891899 50000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (101017221/500000000 : ℝ)^8461 ≤ (606152788101/5000000000000 : ℝ)^6413 := by
    have hnat : (101017221 : ℕ)^8461*5000000000000^6413 ≤ 606152788101^6413*500000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      101017221 500000000 606152788101 5000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8461/2048 : ℝ)) 8461 6413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5306234143/10000000000 : ℝ), (2708398717/5000000000 : ℝ), (-101017221/500000000 : ℝ)] ![(21670383217347/50000000000000 : ℝ), (22268088891899/50000000000000 : ℝ), (606152788101/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5306234143/10000000000 : ℝ)|^8461 ≤ (21670383217347/50000000000000 : ℝ)^6413
        have hw : |(5306234143/10000000000 : ℝ)|=(5306234143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2708398717/5000000000 : ℝ)|^8461 ≤ (22268088891899/50000000000000 : ℝ)^6413
        have hw : |(2708398717/5000000000 : ℝ)|=(2708398717/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-101017221/500000000 : ℝ)|^8461 ≤ (606152788101/5000000000000 : ℝ)^6413
        have hw : |(-101017221/500000000 : ℝ)|=(101017221/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1268_s3_7 (p : ℝ) (hpa : (2115/512 : ℝ) ≤ p) (hpb : p ≤ (8461/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (108641749/250000000 : ℝ)*x 0 + (905228697/2000000000 : ℝ)*x 1 + (4172206633/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (108641749/250000000 : ℝ)^8461 ≤ (6660390283737/20000000000000 : ℝ)^6413 := by
    have hnat : (108641749 : ℕ)^8461*20000000000000^6413 ≤ 6660390283737^6413*250000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      108641749 250000000 6660390283737 20000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (905228697/2000000000 : ℝ)^8461 ≤ (17569310029481/50000000000000 : ℝ)^6413 := by
    have hnat : (905228697 : ℕ)^8461*50000000000000^6413 ≤ 17569310029481^6413*2000000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      905228697 2000000000 17569310029481 50000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4172206633/10000000000 : ℝ)^8461 ≤ (15779714250983/50000000000000 : ℝ)^6413 := by
    have hnat : (4172206633 : ℕ)^8461*50000000000000^6413 ≤ 15779714250983^6413*10000000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4172206633 10000000000 15779714250983 50000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8461/2048 : ℝ)) 8461 6413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(108641749/250000000 : ℝ), (905228697/2000000000 : ℝ), (4172206633/10000000000 : ℝ)] ![(6660390283737/20000000000000 : ℝ), (17569310029481/50000000000000 : ℝ), (15779714250983/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(108641749/250000000 : ℝ)|^8461 ≤ (6660390283737/20000000000000 : ℝ)^6413
        have hw : |(108641749/250000000 : ℝ)|=(108641749/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(905228697/2000000000 : ℝ)|^8461 ≤ (17569310029481/50000000000000 : ℝ)^6413
        have hw : |(905228697/2000000000 : ℝ)|=(905228697/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4172206633/10000000000 : ℝ)|^8461 ≤ (15779714250983/50000000000000 : ℝ)^6413
        have hw : |(4172206633/10000000000 : ℝ)|=(4172206633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1268_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2115/512 : ℝ) ≤ p) (hpb : p ≤ (8461/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151937971/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4039/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9603/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (343/3125 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7339/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4039/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9603/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4039/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9603/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4039/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9603/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4039/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9603/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4039/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9603/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4039/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9603/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9603/100000 : ℝ) ^ (2115/512 : ℝ) ≤ (6258440420483699/100000000000000000000 : ℝ) := by
    have hpowers : (9603/100000 : ℝ)^2115 ≤ (6258440420483699/100000000000000000000 : ℝ)^512 := by
      have hnat : (9603 : ℕ)^2115*100000000000000000000^512 ≤ 6258440420483699^512*100000^2115 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9603 100000 6258440420483699 100000000000000000000 2115 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9603/100000 : ℝ)) (X := (6258440420483699/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2115 512 (by norm_num) hpowers
    exact h
  have hpowhi : (4039/25000 : ℝ) ^ (2115/512 : ℝ) ≤ (26835422917129313/50000000000000000000 : ℝ) := by
    have hpowers : (4039/25000 : ℝ)^2115 ≤ (26835422917129313/50000000000000000000 : ℝ)^512 := by
      have hnat : (4039 : ℕ)^2115*50000000000000000000^512 ≤ 26835422917129313^512*25000^2115 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4039 25000 26835422917129313 50000000000000000000 2115 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4039/25000 : ℝ)) (X := (26835422917129313/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2115 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50006258440420483699/50000000000000000000 : ℝ) ≤ (2000060598950597/2000000000000000 : ℝ) ^ (2115/512 : ℝ) := by
    have hpowers : (50006258440420483699/50000000000000000000 : ℝ)^512 ≤ (2000060598950597/2000000000000000 : ℝ)^2115 := by
      have hnat : (50006258440420483699 : ℕ)^512*2000000000000000^2115 ≤ 2000060598950597^2115*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50006258440420483699 50000000000000000000 2000060598950597 2000000000000000 512 2115 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000060598950597/2000000000000000 : ℝ)) (X := (50006258440420483699/50000000000000000000 : ℝ)) (by norm_num) 2115 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (4002397171450189693/4000000000000000000 : ℝ) ≤ (100014504410627/100000000000000 : ℝ) ^ (2115/512 : ℝ) := by
    have hpowers : (4002397171450189693/4000000000000000000 : ℝ)^512 ≤ (100014504410627/100000000000000 : ℝ)^2115 := by
      have hnat : (4002397171450189693 : ℕ)^512*100000000000000^2115 ≤ 100014504410627^2115*4000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4002397171450189693 4000000000000000000 100014504410627 100000000000000 512 2115 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (100014504410627/100000000000000 : ℝ)) (X := (4002397171450189693/4000000000000000000 : ℝ)) (by norm_num) 2115 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (25026835422917129313/25000000000000000000 : ℝ) ≤ (2000519577474483/2000000000000000 : ℝ) ^ (2115/512 : ℝ) := by
    have hpowers : (25026835422917129313/25000000000000000000 : ℝ)^512 ≤ (2000519577474483/2000000000000000 : ℝ)^2115 := by
      have hnat : (25026835422917129313 : ℕ)^512*2000000000000000^2115 ≤ 2000519577474483^2115*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25026835422917129313 25000000000000000000 2000519577474483 2000000000000000 512 2115 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000519577474483/2000000000000000 : ℝ)) (X := (25026835422917129313/25000000000000000000 : ℝ)) (by norm_num) 2115 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6258440420483699/100000000000000000000 : ℝ) ≤ ((13101989534158384883/13106000000000000000 : ℝ)+2*(229489261943/131060000000000 : ℝ)*(9603/100000 : ℝ))^(2115/512 : ℝ) := by
    rw [show (13101989534158384883/13106000000000000000 : ℝ)+2*(229489261943/131060000000000 : ℝ)*(9603/100000 : ℝ)=(2000060598950597/2000000000000000 : ℝ) by norm_num, show 1+2*(6258440420483699/100000000000000000000 : ℝ)=(50006258440420483699/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(26835422917129313/50000000000000000000 : ℝ)+(6258440420483699/100000000000000000000 : ℝ) ≤ ((13101989534158384883/13106000000000000000 : ℝ)+(229489261943/131060000000000 : ℝ)*((4039/25000 : ℝ)+(9603/100000 : ℝ)))^(2115/512 : ℝ) := by
    rw [show (13101989534158384883/13106000000000000000 : ℝ)+(229489261943/131060000000000 : ℝ)*((4039/25000 : ℝ)+(9603/100000 : ℝ))=(100014504410627/100000000000000 : ℝ) by norm_num, show 1+(26835422917129313/50000000000000000000 : ℝ)+(6258440420483699/100000000000000000000 : ℝ)=(4002397171450189693/4000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(26835422917129313/50000000000000000000 : ℝ) ≤ ((13101989534158384883/13106000000000000000 : ℝ)+2*(229489261943/131060000000000 : ℝ)*(4039/25000 : ℝ))^(2115/512 : ℝ) := by
    rw [show (13101989534158384883/13106000000000000000 : ℝ)+2*(229489261943/131060000000000 : ℝ)*(4039/25000 : ℝ)=(2000519577474483/2000000000000000 : ℝ) by norm_num, show 1+2*(26835422917129313/50000000000000000000 : ℝ)=(25026835422917129313/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13101989534158384883/13106000000000000000 : ℝ)*(X 1 0+X 2 0)+(229489261943/131060000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2115/512 : ℝ)) (lo := (9603/100000 : ℝ)) (hi := (4039/25000 : ℝ)) (c := (13101989534158384883/13106000000000000000 : ℝ)) (alpha := (229489261943/131060000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13101989534158384883/13106000000000000000 : ℝ)*(X 0 1+X 2 1)+(229489261943/131060000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2115/512 : ℝ)) (lo := (9603/100000 : ℝ)) (hi := (4039/25000 : ℝ)) (c := (13101989534158384883/13106000000000000000 : ℝ)) (alpha := (229489261943/131060000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13101989534158384883/13106000000000000000 : ℝ)*(X 0 2+X 1 2)+(229489261943/131060000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2115/512 : ℝ)) (lo := (9603/100000 : ℝ)) (hi := (4039/25000 : ℝ)) (c := (13101989534158384883/13106000000000000000 : ℝ)) (alpha := (229489261943/131060000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2105413831/10000000000 : ℝ)*X 0 0+(5417426363/10000000000 : ℝ)*X 0 1+(2621283413/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1268_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5350921863/10000000000 : ℝ)*X 1 0+(-2194575037/10000000000 : ℝ)*X 1 1+(5242566951/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1268_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1337730463/2500000000 : ℝ)*X 2 0+(20478779/39062500 : ℝ)*X 2 1+(-2194574427/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1268_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4345642459/10000000000 : ℝ)*X 0 0+(2085462393/5000000000 : ℝ)*X 0 1+(4527419457/10000000000 : ℝ)*X 0 2+(4345642459/10000000000 : ℝ)*X 1 0+(2085462393/5000000000 : ℝ)*X 1 1+(4527419457/10000000000 : ℝ)*X 1 2+(4345642459/10000000000 : ℝ)*X 2 0+(2085462393/5000000000 : ℝ)*X 2 1+(4527419457/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1268_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-263178459/1250000000 : ℝ)*X 0 0+(1048638459/2000000000 : ℝ)*X 0 1+(1083359431/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1268_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1061246967/2000000000 : ℝ)*X 1 0+(-505086021/2500000000 : ℝ)*X 1 1+(84637453/156250000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1268_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5306234143/10000000000 : ℝ)*X 2 0+(2708398717/5000000000 : ℝ)*X 2 1+(-101017221/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1268_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((108641749/250000000 : ℝ)*X 0 0+(905228697/2000000000 : ℝ)*X 0 1+(4172206633/10000000000 : ℝ)*X 0 2+(108641749/250000000 : ℝ)*X 1 0+(905228697/2000000000 : ℝ)*X 1 1+(4172206633/10000000000 : ℝ)*X 1 2+(108641749/250000000 : ℝ)*X 2 0+(905228697/2000000000 : ℝ)*X 2 1+(4172206633/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1268_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3787525827556104202433158899/327650000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (816658199/50000000000000 : ℝ)*(base19) + (1103375789/100000000000000 : ℝ)*(base23) + (293780597/100000000000000 : ℝ)*(lower2) + (2243193/1250000000000 : ℝ)*(upper5) + (2131022334769417/50000000000000 : ℝ)*(major0) + (2131022334769417/50000000000000 : ℝ)*(major1) + (2131022334769417/50000000000000 : ℝ)*(major2) + (1429728768315311/25000000000000 : ℝ)*(sp0) + (5718962141358241/100000000000000 : ℝ)*(sp1) + (5718966364626101/100000000000000 : ℝ)*(sp2) + (1402553177962243/50000000000000 : ℝ)*(sp3) + (26197370323/50000000000000 : ℝ)*(sp4) + (3693327251/100000000000000 : ℝ)*(sp5) + (15129828957/100000000000000 : ℝ)*(sp7) + (1402560742876721/50000000000000 : ℝ)*(f.failure) + (571896746800189/10000000000000 : ℝ)*(f.sum) + (1965539762649/819125000000000000000000000 : ℝ)*base66 + (6728846692683276789/655300000000000000000000000000000 : ℝ)*base68 + (1758098866035476789/655300000000000000000000000000000 : ℝ)*base70 + (3761970096751976789/655300000000000000000000000000000 : ℝ)*base72 + (9493794524479/3276500000000000000000000000 : ℝ)*base74 + (3438922729983176789/655300000000000000000000000000000 : ℝ)*base76 + (9697249903017176789/655300000000000000000000000000000 : ℝ)*base78 + (6584966195097876789/655300000000000000000000000000000 : ℝ)*base80 + (10587275993803/3276500000000000000000000000 : ℝ)*base82 + (8126909/5000000000000000000000 : ℝ)*base90 + (8126909/5000000000000000000000 : ℝ)*base92 + (8126909/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (143990928323139804238890171/32765000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2891529937/100000000000000 : ℝ)*(base19) + (200950721/10000000000000 : ℝ)*(base23) + (1576103/4000000000000 : ℝ)*(upper3) + (42350923/100000000000000 : ℝ)*(lower4) + (452195657/100000000000000 : ℝ)*(upper5) + (214639193762607/5000000000000 : ℝ)*(major0) + (214639193762607/5000000000000 : ℝ)*(major1) + (214639193762607/5000000000000 : ℝ)*(major2) + (34206293879/50000000000000 : ℝ)*(sp1) + (21700524629/50000000000000 : ℝ)*(sp2) + (720026837557499/12500000000000 : ℝ)*(sp4) + (720017924542787/12500000000000 : ℝ)*(sp5) + (1440042322475881/25000000000000 : ℝ)*(sp6) + (1412676451777857/50000000000000 : ℝ)*(sp7) + (1412676451777857/50000000000000 : ℝ)*(f.failure) + (720026837557499/12500000000000 : ℝ)*(f.sum) + (8091618501193/1638250000000000000000000000 : ℝ)*base65 + (325497812916669981/65530000000000000000000000000000 : ℝ)*base67 + (462803556376909981/65530000000000000000000000000000 : ℝ)*base69 + (736515024919949981/65530000000000000000000000000000 : ℝ)*base71 + (233025693489/81912500000000000000000000 : ℝ)*base74 + (1550848163460009981/65530000000000000000000000000000 : ℝ)*base75 + (259589556849929981/65530000000000000000000000000000 : ℝ)*base77 + (1288083240397629981/65530000000000000000000000000000 : ℝ)*base79 + (466865135923/102390625000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (64691853/5000000000000000000000 : ℝ)*base90 + (64691853/5000000000000000000000 : ℝ)*base92 + (64691853/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1268_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2115/512 : ℝ) ≤ p) (hpb : p ≤ (8461/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151937971/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4039/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9603/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (343/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7339/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1268_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1268_s4_0 (p : ℝ) (hpa : (2115/512 : ℝ) ≤ p) (hpb : p ≤ (8461/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-526887077/2500000000 : ℝ)*x 0 + (337279301/625000000 : ℝ)*x 1 + (5262125117/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (526887077/2500000000 : ℝ)^8461 ≤ (12818139798501/100000000000000 : ℝ)^6413 := by
    have hnat : (526887077 : ℕ)^8461*100000000000000^6413 ≤ 12818139798501^6413*2500000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526887077 2500000000 12818139798501 100000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (337279301/625000000 : ℝ)^8461 ≤ (44315794774789/100000000000000 : ℝ)^6413 := by
    have hnat : (337279301 : ℕ)^8461*100000000000000^6413 ≤ 44315794774789^6413*625000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337279301 625000000 44315794774789 100000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5262125117/10000000000 : ℝ)^8461 ≤ (42866065407159/100000000000000 : ℝ)^6413 := by
    have hnat : (5262125117 : ℕ)^8461*100000000000000^6413 ≤ 42866065407159^6413*10000000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5262125117 10000000000 42866065407159 100000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8461/2048 : ℝ)) 8461 6413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-526887077/2500000000 : ℝ), (337279301/625000000 : ℝ), (5262125117/10000000000 : ℝ)] ![(12818139798501/100000000000000 : ℝ), (44315794774789/100000000000000 : ℝ), (42866065407159/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-526887077/2500000000 : ℝ)|^8461 ≤ (12818139798501/100000000000000 : ℝ)^6413
        have hw : |(-526887077/2500000000 : ℝ)|=(526887077/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(337279301/625000000 : ℝ)|^8461 ≤ (44315794774789/100000000000000 : ℝ)^6413
        have hw : |(337279301/625000000 : ℝ)|=(337279301/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5262125117/10000000000 : ℝ)|^8461 ≤ (42866065407159/100000000000000 : ℝ)^6413
        have hw : |(5262125117/10000000000 : ℝ)|=(5262125117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1268_s4_1 (p : ℝ) (hpa : (2115/512 : ℝ) ≤ p) (hpb : p ≤ (8461/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5345626749/10000000000 : ℝ)*x 0 + (-2175742501/10000000000 : ℝ)*x 1 + (5262125127/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345626749/10000000000 : ℝ)^8461 ≤ (43765776281063/100000000000000 : ℝ)^6413 := by
    have hnat : (5345626749 : ℕ)^8461*100000000000000^6413 ≤ 43765776281063^6413*10000000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345626749 10000000000 43765776281063 100000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2175742501/10000000000 : ℝ)^8461 ≤ (6684079096753/50000000000000 : ℝ)^6413 := by
    have hnat : (2175742501 : ℕ)^8461*50000000000000^6413 ≤ 6684079096753^6413*10000000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2175742501 10000000000 6684079096753 50000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5262125127/10000000000 : ℝ)^8461 ≤ (8573213102927/20000000000000 : ℝ)^6413 := by
    have hnat : (5262125127 : ℕ)^8461*20000000000000^6413 ≤ 8573213102927^6413*10000000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5262125127 10000000000 8573213102927 20000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8461/2048 : ℝ)) 8461 6413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345626749/10000000000 : ℝ), (-2175742501/10000000000 : ℝ), (5262125127/10000000000 : ℝ)] ![(43765776281063/100000000000000 : ℝ), (6684079096753/50000000000000 : ℝ), (8573213102927/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345626749/10000000000 : ℝ)|^8461 ≤ (43765776281063/100000000000000 : ℝ)^6413
        have hw : |(5345626749/10000000000 : ℝ)|=(5345626749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2175742501/10000000000 : ℝ)|^8461 ≤ (6684079096753/50000000000000 : ℝ)^6413
        have hw : |(-2175742501/10000000000 : ℝ)|=(2175742501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5262125127/10000000000 : ℝ)|^8461 ≤ (8573213102927/20000000000000 : ℝ)^6413
        have hw : |(5262125127/10000000000 : ℝ)|=(5262125127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1268_s4_2 (p : ℝ) (hpa : (2115/512 : ℝ) ≤ p) (hpb : p ≤ (8461/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5345626701/10000000000 : ℝ)*x 0 + (5262125149/10000000000 : ℝ)*x 1 + (-271967817/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345626701/10000000000 : ℝ)^8461 ≤ (2735360985161/6250000000000 : ℝ)^6413 := by
    have hnat : (5345626701 : ℕ)^8461*6250000000000^6413 ≤ 2735360985161^6413*10000000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345626701 10000000000 2735360985161 6250000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5262125149/10000000000 : ℝ)^8461 ≤ (42866065751083/100000000000000 : ℝ)^6413 := by
    have hnat : (5262125149 : ℕ)^8461*100000000000000^6413 ≤ 42866065751083^6413*10000000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5262125149 10000000000 42866065751083 100000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (271967817/1250000000 : ℝ)^8461 ≤ (3342039619307/25000000000000 : ℝ)^6413 := by
    have hnat : (271967817 : ℕ)^8461*25000000000000^6413 ≤ 3342039619307^6413*1250000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      271967817 1250000000 3342039619307 25000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8461/2048 : ℝ)) 8461 6413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345626701/10000000000 : ℝ), (5262125149/10000000000 : ℝ), (-271967817/1250000000 : ℝ)] ![(2735360985161/6250000000000 : ℝ), (42866065751083/100000000000000 : ℝ), (3342039619307/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345626701/10000000000 : ℝ)|^8461 ≤ (2735360985161/6250000000000 : ℝ)^6413
        have hw : |(5345626701/10000000000 : ℝ)|=(5345626701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5262125149/10000000000 : ℝ)|^8461 ≤ (42866065751083/100000000000000 : ℝ)^6413
        have hw : |(5262125149/10000000000 : ℝ)|=(5262125149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-271967817/1250000000 : ℝ)|^8461 ≤ (3342039619307/25000000000000 : ℝ)^6413
        have hw : |(-271967817/1250000000 : ℝ)|=(271967817/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1268_s4_3 (p : ℝ) (hpa : (2115/512 : ℝ) ≤ p) (hpb : p ≤ (8461/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (108673119/250000000 : ℝ)*x 0 + (4212061913/10000000000 : ℝ)*x 1 + (4485956363/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (108673119/250000000 : ℝ)^8461 ≤ (33314638681313/100000000000000 : ℝ)^6413 := by
    have hnat : (108673119 : ℕ)^8461*100000000000000^6413 ≤ 33314638681313^6413*250000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      108673119 250000000 33314638681313 100000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4212061913/10000000000 : ℝ)^8461 ≤ (15978891691473/50000000000000 : ℝ)^6413 := by
    have hnat : (4212061913 : ℕ)^8461*50000000000000^6413 ≤ 15978891691473^6413*10000000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4212061913 10000000000 15978891691473 50000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4485956363/10000000000 : ℝ)^8461 ≤ (34727577922989/100000000000000 : ℝ)^6413 := by
    have hnat : (4485956363 : ℕ)^8461*100000000000000^6413 ≤ 34727577922989^6413*10000000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4485956363 10000000000 34727577922989 100000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8461/2048 : ℝ)) 8461 6413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(108673119/250000000 : ℝ), (4212061913/10000000000 : ℝ), (4485956363/10000000000 : ℝ)] ![(33314638681313/100000000000000 : ℝ), (15978891691473/50000000000000 : ℝ), (34727577922989/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(108673119/250000000 : ℝ)|^8461 ≤ (33314638681313/100000000000000 : ℝ)^6413
        have hw : |(108673119/250000000 : ℝ)|=(108673119/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4212061913/10000000000 : ℝ)|^8461 ≤ (15978891691473/50000000000000 : ℝ)^6413
        have hw : |(4212061913/10000000000 : ℝ)|=(4212061913/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4485956363/10000000000 : ℝ)|^8461 ≤ (34727577922989/100000000000000 : ℝ)^6413
        have hw : |(4485956363/10000000000 : ℝ)|=(4485956363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1268_s4_4 (p : ℝ) (hpa : (2115/512 : ℝ) ≤ p) (hpb : p ≤ (8461/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2107554477/10000000000 : ℝ)*x 0 + (2631247577/5000000000 : ℝ)*x 1 + (539609717/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2107554477/10000000000 : ℝ)^8461 ≤ (6409094650259/50000000000000 : ℝ)^6413 := by
    have hnat : (2107554477 : ℕ)^8461*50000000000000^6413 ≤ 6409094650259^6413*10000000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2107554477 10000000000 6409094650259 50000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2631247577/5000000000 : ℝ)^8461 ≤ (10717510618603/25000000000000 : ℝ)^6413 := by
    have hnat : (2631247577 : ℕ)^8461*25000000000000^6413 ≤ 10717510618603^6413*5000000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2631247577 5000000000 10717510618603 25000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (539609717/1000000000 : ℝ)^8461 ≤ (44311768216291/100000000000000 : ℝ)^6413 := by
    have hnat : (539609717 : ℕ)^8461*100000000000000^6413 ≤ 44311768216291^6413*1000000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539609717 1000000000 44311768216291 100000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8461/2048 : ℝ)) 8461 6413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2107554477/10000000000 : ℝ), (2631247577/5000000000 : ℝ), (539609717/1000000000 : ℝ)] ![(6409094650259/50000000000000 : ℝ), (10717510618603/25000000000000 : ℝ), (44311768216291/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2107554477/10000000000 : ℝ)|^8461 ≤ (6409094650259/50000000000000 : ℝ)^6413
        have hw : |(-2107554477/10000000000 : ℝ)|=(2107554477/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2631247577/5000000000 : ℝ)|^8461 ≤ (10717510618603/25000000000000 : ℝ)^6413
        have hw : |(2631247577/5000000000 : ℝ)|=(2631247577/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(539609717/1000000000 : ℝ)|^8461 ≤ (44311768216291/100000000000000 : ℝ)^6413
        have hw : |(539609717/1000000000 : ℝ)|=(539609717/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1268_s4_5 (p : ℝ) (hpa : (2115/512 : ℝ) ≤ p) (hpb : p ≤ (8461/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2655645087/5000000000 : ℝ)*x 0 + (-2041770613/10000000000 : ℝ)*x 1 + (1079219497/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2655645087/5000000000 : ℝ)^8461 ≤ (339025469921/781250000000 : ℝ)^6413 := by
    have hnat : (2655645087 : ℕ)^8461*781250000000^6413 ≤ 339025469921^6413*5000000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2655645087 5000000000 339025469921 781250000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2041770613/10000000000 : ℝ)^8461 ≤ (1229296821489/10000000000000 : ℝ)^6413 := by
    have hnat : (2041770613 : ℕ)^8461*10000000000000^6413 ≤ 1229296821489^6413*10000000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2041770613 10000000000 1229296821489 10000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1079219497/2000000000 : ℝ)^8461 ≤ (44311771629087/100000000000000 : ℝ)^6413 := by
    have hnat : (1079219497 : ℕ)^8461*100000000000000^6413 ≤ 44311771629087^6413*2000000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1079219497 2000000000 44311771629087 100000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8461/2048 : ℝ)) 8461 6413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2655645087/5000000000 : ℝ), (-2041770613/10000000000 : ℝ), (1079219497/2000000000 : ℝ)] ![(339025469921/781250000000 : ℝ), (1229296821489/10000000000000 : ℝ), (44311771629087/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2655645087/5000000000 : ℝ)|^8461 ≤ (339025469921/781250000000 : ℝ)^6413
        have hw : |(2655645087/5000000000 : ℝ)|=(2655645087/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2041770613/10000000000 : ℝ)|^8461 ≤ (1229296821489/10000000000000 : ℝ)^6413
        have hw : |(-2041770613/10000000000 : ℝ)|=(2041770613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1079219497/2000000000 : ℝ)|^8461 ≤ (44311771629087/100000000000000 : ℝ)^6413
        have hw : |(1079219497/2000000000 : ℝ)|=(1079219497/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1268_s4_6 (p : ℝ) (hpa : (2115/512 : ℝ) ≤ p) (hpb : p ≤ (8461/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5311290117/10000000000 : ℝ)*x 0 + (5396098013/10000000000 : ℝ)*x 1 + (-204176997/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5311290117/10000000000 : ℝ)^8461 ≤ (43395259535451/100000000000000 : ℝ)^6413 := by
    have hnat : (5311290117 : ℕ)^8461*100000000000000^6413 ≤ 43395259535451^6413*10000000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5311290117 10000000000 43395259535451 100000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5396098013/10000000000 : ℝ)^8461 ≤ (44311777349583/100000000000000 : ℝ)^6413 := by
    have hnat : (5396098013 : ℕ)^8461*100000000000000^6413 ≤ 44311777349583^6413*10000000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5396098013 10000000000 44311777349583 100000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (204176997/1000000000 : ℝ)^8461 ≤ (12292963107239/100000000000000 : ℝ)^6413 := by
    have hnat : (204176997 : ℕ)^8461*100000000000000^6413 ≤ 12292963107239^6413*1000000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      204176997 1000000000 12292963107239 100000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8461/2048 : ℝ)) 8461 6413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5311290117/10000000000 : ℝ), (5396098013/10000000000 : ℝ), (-204176997/1000000000 : ℝ)] ![(43395259535451/100000000000000 : ℝ), (44311777349583/100000000000000 : ℝ), (12292963107239/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5311290117/10000000000 : ℝ)|^8461 ≤ (43395259535451/100000000000000 : ℝ)^6413
        have hw : |(5311290117/10000000000 : ℝ)|=(5311290117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5396098013/10000000000 : ℝ)|^8461 ≤ (44311777349583/100000000000000 : ℝ)^6413
        have hw : |(5396098013/10000000000 : ℝ)|=(5396098013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-204176997/1000000000 : ℝ)|^8461 ≤ (12292963107239/100000000000000 : ℝ)^6413
        have hw : |(-204176997/1000000000 : ℝ)|=(204176997/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1268_s4_7 (p : ℝ) (hpa : (2115/512 : ℝ) ≤ p) (hpb : p ≤ (8461/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (217346831/500000000 : ℝ)*x 0 + (4485202947/10000000000 : ℝ)*x 1 + (4212818617/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (217346831/500000000 : ℝ)^8461 ≤ (33314758603163/100000000000000 : ℝ)^6413 := by
    have hnat : (217346831 : ℕ)^8461*100000000000000^6413 ≤ 33314758603163^6413*500000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      217346831 500000000 33314758603163 100000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4485202947/10000000000 : ℝ)^8461 ≤ (34719883020929/100000000000000 : ℝ)^6413 := by
    have hnat : (4485202947 : ℕ)^8461*100000000000000^6413 ≤ 34719883020929^6413*10000000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4485202947 10000000000 34719883020929 100000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4212818617/10000000000 : ℝ)^8461 ≤ (31965358351683/100000000000000 : ℝ)^6413 := by
    have hnat : (4212818617 : ℕ)^8461*100000000000000^6413 ≤ 31965358351683^6413*10000000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4212818617 10000000000 31965358351683 100000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8461/2048 : ℝ)) 8461 6413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(217346831/500000000 : ℝ), (4485202947/10000000000 : ℝ), (4212818617/10000000000 : ℝ)] ![(33314758603163/100000000000000 : ℝ), (34719883020929/100000000000000 : ℝ), (31965358351683/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(217346831/500000000 : ℝ)|^8461 ≤ (33314758603163/100000000000000 : ℝ)^6413
        have hw : |(217346831/500000000 : ℝ)|=(217346831/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4485202947/10000000000 : ℝ)|^8461 ≤ (34719883020929/100000000000000 : ℝ)^6413
        have hw : |(4485202947/10000000000 : ℝ)|=(4485202947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4212818617/10000000000 : ℝ)|^8461 ≤ (31965358351683/100000000000000 : ℝ)^6413
        have hw : |(4212818617/10000000000 : ℝ)|=(4212818617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1268_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2115/512 : ℝ) ≤ p) (hpb : p ≤ (8461/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151937971/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7339/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (343/3125 : ℝ)*pair X i i ≤ pair X i h) :
    (11393/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14239/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7339/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (343/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7339/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (343/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7339/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (343/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7339/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (343/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7339/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (343/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7339/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (343/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (343/3125 : ℝ) ^ (2115/512 : ℝ) ≤ (543474926173999/5000000000000000000 : ℝ) := by
    have hpowers : (343/3125 : ℝ)^2115 ≤ (543474926173999/5000000000000000000 : ℝ)^512 := by
      have hnat : (343 : ℕ)^2115*5000000000000000000^512 ≤ 543474926173999^512*3125^2115 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        343 3125 543474926173999 5000000000000000000 2115 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (343/3125 : ℝ)) (X := (543474926173999/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2115 512 (by norm_num) hpowers
    exact h
  have hpowhi : (7339/50000 : ℝ) ^ (2115/512 : ℝ) ≤ (36109217952029141/100000000000000000000 : ℝ) := by
    have hpowers : (7339/50000 : ℝ)^2115 ≤ (36109217952029141/100000000000000000000 : ℝ)^512 := by
      have hnat : (7339 : ℕ)^2115*100000000000000000000^512 ≤ 36109217952029141^512*50000^2115 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7339 50000 36109217952029141 100000000000000000000 2115 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7339/50000 : ℝ)) (X := (36109217952029141/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2115 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (2500543474926173999/2500000000000000000 : ℝ) ≤ (10000526215114057/10000000000000000 : ℝ) ^ (2115/512 : ℝ) := by
    have hpowers : (2500543474926173999/2500000000000000000 : ℝ)^512 ≤ (10000526215114057/10000000000000000 : ℝ)^2115 := by
      have hnat : (2500543474926173999 : ℕ)^512*10000000000000000^2115 ≤ 10000526215114057^2115*2500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2500543474926173999 2500000000000000000 10000526215114057 10000000000000000 512 2115 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000526215114057/10000000000000000 : ℝ)) (X := (2500543474926173999/2500000000000000000 : ℝ)) (by norm_num) 2115 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100046978716475509121/100000000000000000000 : ℝ) ≤ (5000568530066881/5000000000000000 : ℝ) ^ (2115/512 : ℝ) := by
    have hpowers : (100046978716475509121/100000000000000000000 : ℝ)^512 ≤ (5000568530066881/5000000000000000 : ℝ)^2115 := by
      have hnat : (100046978716475509121 : ℕ)^512*5000000000000000^2115 ≤ 5000568530066881^2115*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100046978716475509121 100000000000000000000 5000568530066881 5000000000000000 512 2115 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000568530066881/5000000000000000 : ℝ)) (X := (100046978716475509121/100000000000000000000 : ℝ)) (by norm_num) 2115 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50036109217952029141/50000000000000000000 : ℝ) ≤ (10001747905153467/10000000000000000 : ℝ) ^ (2115/512 : ℝ) := by
    have hpowers : (50036109217952029141/50000000000000000000 : ℝ)^512 ≤ (10001747905153467/10000000000000000 : ℝ)^2115 := by
      have hnat : (50036109217952029141 : ℕ)^512*10000000000000000^2115 ≤ 10001747905153467^2115*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50036109217952029141 50000000000000000000 10001747905153467 10000000000000000 512 2115 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001747905153467/10000000000000000 : ℝ)) (X := (50036109217952029141/50000000000000000000 : ℝ)) (by norm_num) 2115 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(543474926173999/5000000000000000000 : ℝ) ≤ ((18504269389239837427/18510000000000000000 : ℝ)+2*(122169003941/74040000000000 : ℝ)*(343/3125 : ℝ))^(2115/512 : ℝ) := by
    rw [show (18504269389239837427/18510000000000000000 : ℝ)+2*(122169003941/74040000000000 : ℝ)*(343/3125 : ℝ)=(10000526215114057/10000000000000000 : ℝ) by norm_num, show 1+2*(543474926173999/5000000000000000000 : ℝ)=(2500543474926173999/2500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(36109217952029141/100000000000000000000 : ℝ)+(543474926173999/5000000000000000000 : ℝ) ≤ ((18504269389239837427/18510000000000000000 : ℝ)+(122169003941/74040000000000 : ℝ)*((7339/50000 : ℝ)+(343/3125 : ℝ)))^(2115/512 : ℝ) := by
    rw [show (18504269389239837427/18510000000000000000 : ℝ)+(122169003941/74040000000000 : ℝ)*((7339/50000 : ℝ)+(343/3125 : ℝ))=(5000568530066881/5000000000000000 : ℝ) by norm_num, show 1+(36109217952029141/100000000000000000000 : ℝ)+(543474926173999/5000000000000000000 : ℝ)=(100046978716475509121/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(36109217952029141/100000000000000000000 : ℝ) ≤ ((18504269389239837427/18510000000000000000 : ℝ)+2*(122169003941/74040000000000 : ℝ)*(7339/50000 : ℝ))^(2115/512 : ℝ) := by
    rw [show (18504269389239837427/18510000000000000000 : ℝ)+2*(122169003941/74040000000000 : ℝ)*(7339/50000 : ℝ)=(10001747905153467/10000000000000000 : ℝ) by norm_num, show 1+2*(36109217952029141/100000000000000000000 : ℝ)=(50036109217952029141/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (18504269389239837427/18510000000000000000 : ℝ)*(X 1 0+X 2 0)+(122169003941/74040000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2115/512 : ℝ)) (lo := (343/3125 : ℝ)) (hi := (7339/50000 : ℝ)) (c := (18504269389239837427/18510000000000000000 : ℝ)) (alpha := (122169003941/74040000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (18504269389239837427/18510000000000000000 : ℝ)*(X 0 1+X 2 1)+(122169003941/74040000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2115/512 : ℝ)) (lo := (343/3125 : ℝ)) (hi := (7339/50000 : ℝ)) (c := (18504269389239837427/18510000000000000000 : ℝ)) (alpha := (122169003941/74040000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (18504269389239837427/18510000000000000000 : ℝ)*(X 0 2+X 1 2)+(122169003941/74040000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2115/512 : ℝ)) (lo := (343/3125 : ℝ)) (hi := (7339/50000 : ℝ)) (c := (18504269389239837427/18510000000000000000 : ℝ)) (alpha := (122169003941/74040000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-526887077/2500000000 : ℝ)*X 0 0+(337279301/625000000 : ℝ)*X 0 1+(5262125117/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1268_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5345626749/10000000000 : ℝ)*X 1 0+(-2175742501/10000000000 : ℝ)*X 1 1+(5262125127/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1268_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5345626701/10000000000 : ℝ)*X 2 0+(5262125149/10000000000 : ℝ)*X 2 1+(-271967817/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1268_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((108673119/250000000 : ℝ)*X 0 0+(4212061913/10000000000 : ℝ)*X 0 1+(4485956363/10000000000 : ℝ)*X 0 2+(108673119/250000000 : ℝ)*X 1 0+(4212061913/10000000000 : ℝ)*X 1 1+(4485956363/10000000000 : ℝ)*X 1 2+(108673119/250000000 : ℝ)*X 2 0+(4212061913/10000000000 : ℝ)*X 2 1+(4485956363/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1268_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2107554477/10000000000 : ℝ)*X 0 0+(2631247577/5000000000 : ℝ)*X 0 1+(539609717/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1268_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2655645087/5000000000 : ℝ)*X 1 0+(-2041770613/10000000000 : ℝ)*X 1 1+(1079219497/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1268_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5311290117/10000000000 : ℝ)*X 2 0+(5396098013/10000000000 : ℝ)*X 2 1+(-204176997/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1268_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((217346831/500000000 : ℝ)*X 0 0+(4485202947/10000000000 : ℝ)*X 0 1+(4212818617/10000000000 : ℝ)*X 0 2+(217346831/500000000 : ℝ)*X 1 0+(4485202947/10000000000 : ℝ)*X 1 1+(4212818617/10000000000 : ℝ)*X 1 2+(217346831/500000000 : ℝ)*X 2 0+(4485202947/10000000000 : ℝ)*X 2 1+(4212818617/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1268_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (836595648668249030334654111/77125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2229223357/100000000000000 : ℝ)*(base19) + (199889293/10000000000000 : ℝ)*(base23) + (21849061/25000000000000 : ℝ)*(lower2) + (322837543/100000000000000 : ℝ)*(upper3) + (68051377/50000000000000 : ℝ)*(upper5) + (2773702690669293/50000000000000 : ℝ)*(major0) + (2773702690669293/50000000000000 : ℝ)*(major1) + (2773702690669293/50000000000000 : ℝ)*(major2) + (3721828171542947/50000000000000 : ℝ)*(sp0) + (3721854703902581/50000000000000 : ℝ)*(sp1) + (7443709638135589/100000000000000 : ℝ)*(sp2) + (456383502791721/12500000000000 : ℝ)*(sp3) + (1727935707/3125000000000 : ℝ)*(sp4) + (30741739229/100000000000000 : ℝ)*(sp7) + (912774691018249/25000000000000 : ℝ)*(f.failure) + (3721855818514259/50000000000000 : ℝ)*(f.sum) + (2246380634649/617000000000000000000000000 : ℝ)*base66 + (5036887577076406963/308500000000000000000000000000000 : ℝ)*base68 + (165423780605593037/308500000000000000000000000000000 : ℝ)*base69 + (6821568823359906963/308500000000000000000000000000000 : ℝ)*base72 + (120265833237/308500000000000000000000000 : ℝ)*base74 + (2693116209310406963/308500000000000000000000000000000 : ℝ)*base76 + (3443272798843406963/308500000000000000000000000000000 : ℝ)*base78 + (6213599793744906963/308500000000000000000000000000000 : ℝ)*base80 + (366166246157/61700000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (27032779/2500000000000000000000 : ℝ)*base89 + (27032779/2500000000000000000000 : ℝ)*base91 + (27032779/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (55362923204072357321345903/7712500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (245732963/100000000000000 : ℝ)*(base19) + (689785421/100000000000000 : ℝ)*(base23) + (146777597/100000000000000 : ℝ)*(upper2) + (10903357/3125000000000 : ℝ)*(upper3) + (13704891/25000000000000 : ℝ)*(upper4) + (278905057896289/5000000000000 : ℝ)*(major0) + (278905057896289/5000000000000 : ℝ)*(major1) + (278905057896289/5000000000000 : ℝ)*(major2) + (6791409481/12500000000000 : ℝ)*(sp2) + (5668342439/100000000000000 : ℝ)*(sp3) + (7484900478156381/100000000000000 : ℝ)*(sp4) + (3742450116211709/50000000000000 : ℝ)*(sp5) + (935605682136889/12500000000000 : ℝ)*(sp6) + (91782398251871/2500000000000 : ℝ)*(sp7) + (1835650799208639/50000000000000 : ℝ)*(f.failure) + (7484900478156381/100000000000000 : ℝ)*(f.sum) + (2285554886237/1851000000000000000000000000 : ℝ)*base65 + (184461963338897199/30850000000000000000000000000000 : ℝ)*base68 + (221284318402002801/30850000000000000000000000000000 : ℝ)*base69 + (9251492648247199/30850000000000000000000000000000 : ℝ)*base72 + (6422847312613/1851000000000000000000000000 : ℝ)*base74 + (302960898063997199/30850000000000000000000000000000 : ℝ)*base76 + (74929008445247199/30850000000000000000000000000000 : ℝ)*base78 + (177231838072797199/30850000000000000000000000000000 : ℝ)*base80 + (82928253371/1851000000000000000000000000 : ℝ)*base81 + (15331469/5000000000000000000000 : ℝ)*base89 + (15331469/5000000000000000000000 : ℝ)*base91 + (15331469/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1268_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2115/512 : ℝ) ≤ p) (hpb : p ≤ (8461/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151937971/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7339/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (343/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11393/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14239/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1268_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1268_s5_0 (p : ℝ) (hpa : (2115/512 : ℝ) ≤ p) (hpb : p ≤ (8461/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2107959379/10000000000 : ℝ)*x 0 + (336986959/625000000 : ℝ)*x 1 + (5266532237/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2107959379/10000000000 : ℝ)^8461 ≤ (2564287692811/20000000000000 : ℝ)^6413 := by
    have hnat : (2107959379 : ℕ)^8461*20000000000000^6413 ≤ 2564287692811^6413*10000000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2107959379 10000000000 2564287692811 20000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (336986959/625000000 : ℝ)^8461 ≤ (44265123666969/100000000000000 : ℝ)^6413 := by
    have hnat : (336986959 : ℕ)^8461*100000000000000^6413 ≤ 44265123666969^6413*625000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      336986959 625000000 44265123666969 100000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266532237/10000000000 : ℝ)^8461 ≤ (10728359464317/25000000000000 : ℝ)^6413 := by
    have hnat : (5266532237 : ℕ)^8461*25000000000000^6413 ≤ 10728359464317^6413*10000000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266532237 10000000000 10728359464317 25000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8461/2048 : ℝ)) 8461 6413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2107959379/10000000000 : ℝ), (336986959/625000000 : ℝ), (5266532237/10000000000 : ℝ)] ![(2564287692811/20000000000000 : ℝ), (44265123666969/100000000000000 : ℝ), (10728359464317/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2107959379/10000000000 : ℝ)|^8461 ≤ (2564287692811/20000000000000 : ℝ)^6413
        have hw : |(-2107959379/10000000000 : ℝ)|=(2107959379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(336986959/625000000 : ℝ)|^8461 ≤ (44265123666969/100000000000000 : ℝ)^6413
        have hw : |(336986959/625000000 : ℝ)|=(336986959/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266532237/10000000000 : ℝ)|^8461 ≤ (10728359464317/25000000000000 : ℝ)^6413
        have hw : |(5266532237/10000000000 : ℝ)|=(5266532237/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1268_s5_1 (p : ℝ) (hpa : (2115/512 : ℝ) ≤ p) (hpb : p ≤ (8461/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1336110143/2500000000 : ℝ)*x 0 + (-434295571/2000000000 : ℝ)*x 1 + (2633266113/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336110143/2500000000 : ℝ)^8461 ≤ (21876481939337/50000000000000 : ℝ)^6413 := by
    have hnat : (1336110143 : ℕ)^8461*50000000000000^6413 ≤ 21876481939337^6413*2500000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336110143 2500000000 21876481939337 50000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (434295571/2000000000 : ℝ)^8461 ≤ (13333598369953/100000000000000 : ℝ)^6413 := by
    have hnat : (434295571 : ℕ)^8461*100000000000000^6413 ≤ 13333598369953^6413*2000000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      434295571 2000000000 13333598369953 100000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2633266113/5000000000 : ℝ)^8461 ≤ (10728359434753/25000000000000 : ℝ)^6413 := by
    have hnat : (2633266113 : ℕ)^8461*25000000000000^6413 ≤ 10728359434753^6413*5000000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633266113 5000000000 10728359434753 25000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8461/2048 : ℝ)) 8461 6413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336110143/2500000000 : ℝ), (-434295571/2000000000 : ℝ), (2633266113/5000000000 : ℝ)] ![(21876481939337/50000000000000 : ℝ), (13333598369953/100000000000000 : ℝ), (10728359434753/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336110143/2500000000 : ℝ)|^8461 ≤ (21876481939337/50000000000000 : ℝ)^6413
        have hw : |(1336110143/2500000000 : ℝ)|=(1336110143/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-434295571/2000000000 : ℝ)|^8461 ≤ (13333598369953/100000000000000 : ℝ)^6413
        have hw : |(-434295571/2000000000 : ℝ)|=(434295571/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2633266113/5000000000 : ℝ)|^8461 ≤ (10728359434753/25000000000000 : ℝ)^6413
        have hw : |(2633266113/5000000000 : ℝ)|=(2633266113/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1268_s5_2 (p : ℝ) (hpa : (2115/512 : ℝ) ≤ p) (hpb : p ≤ (8461/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672220283/5000000000 : ℝ)*x 0 + (5266532253/10000000000 : ℝ)*x 1 + (-2171477827/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672220283/5000000000 : ℝ)^8461 ≤ (10938240953467/25000000000000 : ℝ)^6413 := by
    have hnat : (2672220283 : ℕ)^8461*25000000000000^6413 ≤ 10938240953467^6413*5000000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672220283 5000000000 10938240953467 25000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266532253/10000000000 : ℝ)^8461 ≤ (10728359507319/25000000000000 : ℝ)^6413 := by
    have hnat : (5266532253 : ℕ)^8461*25000000000000^6413 ≤ 10728359507319^6413*10000000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266532253 10000000000 10728359507319 25000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2171477827/10000000000 : ℝ)^8461 ≤ (6666799071559/50000000000000 : ℝ)^6413 := by
    have hnat : (2171477827 : ℕ)^8461*50000000000000^6413 ≤ 6666799071559^6413*10000000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2171477827 10000000000 6666799071559 50000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8461/2048 : ℝ)) 8461 6413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672220283/5000000000 : ℝ), (5266532253/10000000000 : ℝ), (-2171477827/10000000000 : ℝ)] ![(10938240953467/25000000000000 : ℝ), (10728359507319/25000000000000 : ℝ), (6666799071559/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672220283/5000000000 : ℝ)|^8461 ≤ (10938240953467/25000000000000 : ℝ)^6413
        have hw : |(2672220283/5000000000 : ℝ)|=(2672220283/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266532253/10000000000 : ℝ)|^8461 ≤ (10728359507319/25000000000000 : ℝ)^6413
        have hw : |(5266532253/10000000000 : ℝ)|=(5266532253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2171477827/10000000000 : ℝ)|^8461 ≤ (6666799071559/50000000000000 : ℝ)^6413
        have hw : |(-2171477827/10000000000 : ℝ)|=(2171477827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1268_s5_3 (p : ℝ) (hpa : (2115/512 : ℝ) ≤ p) (hpb : p ≤ (8461/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (3477733/8000000 : ℝ)*x 0 + (131915367/312500000 : ℝ)*x 1 + (4476665057/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3477733/8000000 : ℝ)^8461 ≤ (16658540258519/50000000000000 : ℝ)^6413 := by
    have hnat : (3477733 : ℕ)^8461*50000000000000^6413 ≤ 16658540258519^6413*8000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3477733 8000000 16658540258519 50000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (131915367/312500000 : ℝ)^8461 ≤ (16025104032163/50000000000000 : ℝ)^6413 := by
    have hnat : (131915367 : ℕ)^8461*50000000000000^6413 ≤ 16025104032163^6413*312500000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131915367 312500000 16025104032163 50000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4476665057/10000000000 : ℝ)^8461 ≤ (34632711407903/100000000000000 : ℝ)^6413 := by
    have hnat : (4476665057 : ℕ)^8461*100000000000000^6413 ≤ 34632711407903^6413*10000000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4476665057 10000000000 34632711407903 100000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8461/2048 : ℝ)) 8461 6413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3477733/8000000 : ℝ), (131915367/312500000 : ℝ), (4476665057/10000000000 : ℝ)] ![(16658540258519/50000000000000 : ℝ), (16025104032163/50000000000000 : ℝ), (34632711407903/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3477733/8000000 : ℝ)|^8461 ≤ (16658540258519/50000000000000 : ℝ)^6413
        have hw : |(3477733/8000000 : ℝ)|=(3477733/8000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(131915367/312500000 : ℝ)|^8461 ≤ (16025104032163/50000000000000 : ℝ)^6413
        have hw : |(131915367/312500000 : ℝ)|=(131915367/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4476665057/10000000000 : ℝ)|^8461 ≤ (34632711407903/100000000000000 : ℝ)^6413
        have hw : |(4476665057/10000000000 : ℝ)|=(4476665057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1268_s5_4 (p : ℝ) (hpa : (2115/512 : ℝ) ≤ p) (hpb : p ≤ (8461/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2107964151/10000000000 : ℝ)*x 0 + (5266853789/10000000000 : ℝ)*x 1 + (1078293731/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2107964151/10000000000 : ℝ)^8461 ≤ (12821476758481/100000000000000 : ℝ)^6413 := by
    have hnat : (2107964151 : ℕ)^8461*100000000000000^6413 ≤ 12821476758481^6413*10000000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2107964151 10000000000 12821476758481 100000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266853789/10000000000 : ℝ)^8461 ≤ (42916894738551/100000000000000 : ℝ)^6413 := by
    have hnat : (5266853789 : ℕ)^8461*100000000000000^6413 ≤ 42916894738551^6413*10000000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266853789 10000000000 42916894738551 100000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1078293731/2000000000 : ℝ)^8461 ≤ (44261628490799/100000000000000 : ℝ)^6413 := by
    have hnat : (1078293731 : ℕ)^8461*100000000000000^6413 ≤ 44261628490799^6413*2000000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078293731 2000000000 44261628490799 100000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8461/2048 : ℝ)) 8461 6413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2107964151/10000000000 : ℝ), (5266853789/10000000000 : ℝ), (1078293731/2000000000 : ℝ)] ![(12821476758481/100000000000000 : ℝ), (42916894738551/100000000000000 : ℝ), (44261628490799/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2107964151/10000000000 : ℝ)|^8461 ≤ (12821476758481/100000000000000 : ℝ)^6413
        have hw : |(-2107964151/10000000000 : ℝ)|=(2107964151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266853789/10000000000 : ℝ)|^8461 ≤ (42916894738551/100000000000000 : ℝ)^6413
        have hw : |(5266853789/10000000000 : ℝ)|=(5266853789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1078293731/2000000000 : ℝ)|^8461 ≤ (44261628490799/100000000000000 : ℝ)^6413
        have hw : |(1078293731/2000000000 : ℝ)|=(1078293731/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1268_s5_5 (p : ℝ) (hpa : (2115/512 : ℝ) ≤ p) (hpb : p ≤ (8461/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312424911/10000000000 : ℝ)*x 0 + (-1023270699/5000000000 : ℝ)*x 1 + (1347867163/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312424911/10000000000 : ℝ)^8461 ≤ (1736299703211/4000000000000 : ℝ)^6413 := by
    have hnat : (5312424911 : ℕ)^8461*4000000000000^6413 ≤ 1736299703211^6413*10000000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312424911 10000000000 1736299703211 4000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1023270699/5000000000 : ℝ)^8461 ≤ (12330878934493/100000000000000 : ℝ)^6413 := by
    have hnat : (1023270699 : ℕ)^8461*100000000000000^6413 ≤ 12330878934493^6413*5000000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1023270699 5000000000 12330878934493 100000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1347867163/2500000000 : ℝ)^8461 ≤ (8852325691661/20000000000000 : ℝ)^6413 := by
    have hnat : (1347867163 : ℕ)^8461*20000000000000^6413 ≤ 8852325691661^6413*2500000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1347867163 2500000000 8852325691661 20000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8461/2048 : ℝ)) 8461 6413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312424911/10000000000 : ℝ), (-1023270699/5000000000 : ℝ), (1347867163/2500000000 : ℝ)] ![(1736299703211/4000000000000 : ℝ), (12330878934493/100000000000000 : ℝ), (8852325691661/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312424911/10000000000 : ℝ)|^8461 ≤ (1736299703211/4000000000000 : ℝ)^6413
        have hw : |(5312424911/10000000000 : ℝ)|=(5312424911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1023270699/5000000000 : ℝ)|^8461 ≤ (12330878934493/100000000000000 : ℝ)^6413
        have hw : |(-1023270699/5000000000 : ℝ)|=(1023270699/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1347867163/2500000000 : ℝ)|^8461 ≤ (8852325691661/20000000000000 : ℝ)^6413
        have hw : |(1347867163/2500000000 : ℝ)|=(1347867163/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1268_s5_6 (p : ℝ) (hpa : (2115/512 : ℝ) ≤ p) (hpb : p ≤ (8461/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (132810623/250000000 : ℝ)*x 0 + (2695734323/5000000000 : ℝ)*x 1 + (-2046541397/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (132810623/250000000 : ℝ)^8461 ≤ (21703746338649/50000000000000 : ℝ)^6413 := by
    have hnat : (132810623 : ℕ)^8461*50000000000000^6413 ≤ 21703746338649^6413*250000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132810623 250000000 21703746338649 50000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2695734323/5000000000 : ℝ)^8461 ≤ (44261628393317/100000000000000 : ℝ)^6413 := by
    have hnat : (2695734323 : ℕ)^8461*100000000000000^6413 ≤ 44261628393317^6413*5000000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695734323 5000000000 44261628393317 100000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2046541397/10000000000 : ℝ)^8461 ≤ (770679932909/6250000000000 : ℝ)^6413 := by
    have hnat : (2046541397 : ℕ)^8461*6250000000000^6413 ≤ 770679932909^6413*10000000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2046541397 10000000000 770679932909 6250000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8461/2048 : ℝ)) 8461 6413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(132810623/250000000 : ℝ), (2695734323/5000000000 : ℝ), (-2046541397/10000000000 : ℝ)] ![(21703746338649/50000000000000 : ℝ), (44261628393317/100000000000000 : ℝ), (770679932909/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(132810623/250000000 : ℝ)|^8461 ≤ (21703746338649/50000000000000 : ℝ)^6413
        have hw : |(132810623/250000000 : ℝ)|=(132810623/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2695734323/5000000000 : ℝ)|^8461 ≤ (44261628393317/100000000000000 : ℝ)^6413
        have hw : |(2695734323/5000000000 : ℝ)|=(2695734323/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2046541397/10000000000 : ℝ)|^8461 ≤ (770679932909/6250000000000 : ℝ)^6413
        have hw : |(-2046541397/10000000000 : ℝ)|=(2046541397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1268_s5_7 (p : ℝ) (hpa : (2115/512 : ℝ) ≤ p) (hpb : p ≤ (8461/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (543397003/1250000000 : ℝ)*x 0 + (1119002379/2500000000 : ℝ)*x 1 + (4221949799/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (543397003/1250000000 : ℝ)^8461 ≤ (33317179348139/100000000000000 : ℝ)^6413 := by
    have hnat : (543397003 : ℕ)^8461*100000000000000^6413 ≤ 33317179348139^6413*1250000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      543397003 1250000000 33317179348139 100000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1119002379/2500000000 : ℝ)^8461 ≤ (34626020546229/100000000000000 : ℝ)^6413 := by
    have hnat : (1119002379 : ℕ)^8461*100000000000000^6413 ≤ 34626020546229^6413*2500000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1119002379 2500000000 34626020546229 100000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4221949799/10000000000 : ℝ)^8461 ≤ (8014200022701/25000000000000 : ℝ)^6413 := by
    have hnat : (4221949799 : ℕ)^8461*25000000000000^6413 ≤ 8014200022701^6413*10000000000^8461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4221949799 10000000000 8014200022701 25000000000000 8461 6413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8461/2048 : ℝ)) 8461 6413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(543397003/1250000000 : ℝ), (1119002379/2500000000 : ℝ), (4221949799/10000000000 : ℝ)] ![(33317179348139/100000000000000 : ℝ), (34626020546229/100000000000000 : ℝ), (8014200022701/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(543397003/1250000000 : ℝ)|^8461 ≤ (33317179348139/100000000000000 : ℝ)^6413
        have hw : |(543397003/1250000000 : ℝ)|=(543397003/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1119002379/2500000000 : ℝ)|^8461 ≤ (34626020546229/100000000000000 : ℝ)^6413
        have hw : |(1119002379/2500000000 : ℝ)|=(1119002379/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4221949799/10000000000 : ℝ)|^8461 ≤ (8014200022701/25000000000000 : ℝ)^6413
        have hw : |(4221949799/10000000000 : ℝ)|=(4221949799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1268_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2115/512 : ℝ) ≤ p) (hpb : p ≤ (8461/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151937971/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14239/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11393/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11487/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14141/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14239/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11393/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14239/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11393/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14239/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11393/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14239/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11393/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14239/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11393/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14239/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11393/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11393/100000 : ℝ) ^ (2115/512 : ℝ) ≤ (12679573354564493/100000000000000000000 : ℝ) := by
    have hpowers : (11393/100000 : ℝ)^2115 ≤ (12679573354564493/100000000000000000000 : ℝ)^512 := by
      have hnat : (11393 : ℕ)^2115*100000000000000000000^512 ≤ 12679573354564493^512*100000^2115 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11393 100000 12679573354564493 100000000000000000000 2115 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11393/100000 : ℝ)) (X := (12679573354564493/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2115 512 (by norm_num) hpowers
    exact h
  have hpowhi : (14239/100000 : ℝ) ^ (2115/512 : ℝ) ≤ (31852447988415433/100000000000000000000 : ℝ) := by
    have hpowers : (14239/100000 : ℝ)^2115 ≤ (31852447988415433/100000000000000000000 : ℝ)^512 := by
      have hnat : (14239 : ℕ)^2115*100000000000000000000^512 ≤ 31852447988415433^512*100000^2115 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14239 100000 31852447988415433 100000000000000000000 2115 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14239/100000 : ℝ)) (X := (31852447988415433/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2115 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50012679573354564493/50000000000000000000 : ℝ) ≤ (5000306918097793/5000000000000000 : ℝ) ^ (2115/512 : ℝ) := by
    have hpowers : (50012679573354564493/50000000000000000000 : ℝ)^512 ≤ (5000306918097793/5000000000000000 : ℝ)^2115 := by
      have hnat : (50012679573354564493 : ℕ)^512*5000000000000000^2115 ≤ 5000306918097793^2115*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50012679573354564493 50000000000000000000 5000306918097793 5000000000000000 512 2115 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000306918097793/5000000000000000 : ℝ)) (X := (50012679573354564493/50000000000000000000 : ℝ)) (by norm_num) 2115 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (50022266010671489963/50000000000000000000 : ℝ) ≤ (10001077850977387/10000000000000000 : ℝ) ^ (2115/512 : ℝ) := by
    have hpowers : (50022266010671489963/50000000000000000000 : ℝ)^512 ≤ (10001077850977387/10000000000000000 : ℝ)^2115 := by
      have hnat : (50022266010671489963 : ℕ)^512*10000000000000000^2115 ≤ 10001077850977387^2115*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50022266010671489963 50000000000000000000 10001077850977387 10000000000000000 512 2115 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001077850977387/10000000000000000 : ℝ)) (X := (50022266010671489963/50000000000000000000 : ℝ)) (by norm_num) 2115 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50031852447988415433/50000000000000000000 : ℝ) ≤ (2500385466439797/2500000000000000 : ℝ) ^ (2115/512 : ℝ) := by
    have hpowers : (50031852447988415433/50000000000000000000 : ℝ)^512 ≤ (2500385466439797/2500000000000000 : ℝ)^2115 := by
      have hnat : (50031852447988415433 : ℕ)^512*2500000000000000^2115 ≤ 2500385466439797^2115*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50031852447988415433 50000000000000000000 2500385466439797 2500000000000000 512 2115 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500385466439797/2500000000000000 : ℝ)) (X := (50031852447988415433/50000000000000000000 : ℝ)) (by norm_num) 2115 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(12679573354564493/100000000000000000000 : ℝ) ≤ ((2845117393699452017/2846000000000000000 : ℝ)+2*(464014781801/284600000000000 : ℝ)*(11393/100000 : ℝ))^(2115/512 : ℝ) := by
    rw [show (2845117393699452017/2846000000000000000 : ℝ)+2*(464014781801/284600000000000 : ℝ)*(11393/100000 : ℝ)=(5000306918097793/5000000000000000 : ℝ) by norm_num, show 1+2*(12679573354564493/100000000000000000000 : ℝ)=(50012679573354564493/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(31852447988415433/100000000000000000000 : ℝ)+(12679573354564493/100000000000000000000 : ℝ) ≤ ((2845117393699452017/2846000000000000000 : ℝ)+(464014781801/284600000000000 : ℝ)*((14239/100000 : ℝ)+(11393/100000 : ℝ)))^(2115/512 : ℝ) := by
    rw [show (2845117393699452017/2846000000000000000 : ℝ)+(464014781801/284600000000000 : ℝ)*((14239/100000 : ℝ)+(11393/100000 : ℝ))=(10001077850977387/10000000000000000 : ℝ) by norm_num, show 1+(31852447988415433/100000000000000000000 : ℝ)+(12679573354564493/100000000000000000000 : ℝ)=(50022266010671489963/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(31852447988415433/100000000000000000000 : ℝ) ≤ ((2845117393699452017/2846000000000000000 : ℝ)+2*(464014781801/284600000000000 : ℝ)*(14239/100000 : ℝ))^(2115/512 : ℝ) := by
    rw [show (2845117393699452017/2846000000000000000 : ℝ)+2*(464014781801/284600000000000 : ℝ)*(14239/100000 : ℝ)=(2500385466439797/2500000000000000 : ℝ) by norm_num, show 1+2*(31852447988415433/100000000000000000000 : ℝ)=(50031852447988415433/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2845117393699452017/2846000000000000000 : ℝ)*(X 1 0+X 2 0)+(464014781801/284600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2115/512 : ℝ)) (lo := (11393/100000 : ℝ)) (hi := (14239/100000 : ℝ)) (c := (2845117393699452017/2846000000000000000 : ℝ)) (alpha := (464014781801/284600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2845117393699452017/2846000000000000000 : ℝ)*(X 0 1+X 2 1)+(464014781801/284600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2115/512 : ℝ)) (lo := (11393/100000 : ℝ)) (hi := (14239/100000 : ℝ)) (c := (2845117393699452017/2846000000000000000 : ℝ)) (alpha := (464014781801/284600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2845117393699452017/2846000000000000000 : ℝ)*(X 0 2+X 1 2)+(464014781801/284600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2115/512 : ℝ)) (lo := (11393/100000 : ℝ)) (hi := (14239/100000 : ℝ)) (c := (2845117393699452017/2846000000000000000 : ℝ)) (alpha := (464014781801/284600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2107959379/10000000000 : ℝ)*X 0 0+(336986959/625000000 : ℝ)*X 0 1+(5266532237/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1268_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1336110143/2500000000 : ℝ)*X 1 0+(-434295571/2000000000 : ℝ)*X 1 1+(2633266113/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1268_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672220283/5000000000 : ℝ)*X 2 0+(5266532253/10000000000 : ℝ)*X 2 1+(-2171477827/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1268_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((3477733/8000000 : ℝ)*X 0 0+(131915367/312500000 : ℝ)*X 0 1+(4476665057/10000000000 : ℝ)*X 0 2+(3477733/8000000 : ℝ)*X 1 0+(131915367/312500000 : ℝ)*X 1 1+(4476665057/10000000000 : ℝ)*X 1 2+(3477733/8000000 : ℝ)*X 2 0+(131915367/312500000 : ℝ)*X 2 1+(4476665057/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1268_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2107964151/10000000000 : ℝ)*X 0 0+(5266853789/10000000000 : ℝ)*X 0 1+(1078293731/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1268_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312424911/10000000000 : ℝ)*X 1 0+(-1023270699/5000000000 : ℝ)*X 1 1+(1347867163/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1268_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((132810623/250000000 : ℝ)*X 2 0+(2695734323/5000000000 : ℝ)*X 2 1+(-2046541397/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1268_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((543397003/1250000000 : ℝ)*X 0 0+(1119002379/2500000000 : ℝ)*X 0 1+(4221949799/10000000000 : ℝ)*X 0 2+(543397003/1250000000 : ℝ)*X 1 0+(1119002379/2500000000 : ℝ)*X 1 1+(4221949799/10000000000 : ℝ)*X 1 2+(543397003/1250000000 : ℝ)*X 2 0+(1119002379/2500000000 : ℝ)*X 2 1+(4221949799/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1268_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (177518063766861263366243151/17787500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2008181161/100000000000000 : ℝ)*(base19) + (1896289199/100000000000000 : ℝ)*(base23) + (2750493/5000000000000 : ℝ)*(lower2) + (262860169/100000000000000 : ℝ)*(upper3) + (2890993/1250000000000 : ℝ)*(upper5) + (743715716882899/12500000000000 : ℝ)*(major0) + (743715716882899/12500000000000 : ℝ)*(major1) + (743715716882899/12500000000000 : ℝ)*(major2) + (7983505530601151/100000000000000 : ℝ)*(sp0) + (7983557863980671/100000000000000 : ℝ)*(sp1) + (3991778987936317/50000000000000 : ℝ)*(sp2) + (3915862955114863/100000000000000 : ℝ)*(sp3) + (54341560681/100000000000000 : ℝ)*(sp4) + (28310185233/100000000000000 : ℝ)*(sp7) + (30592900510157/781250000000 : ℝ)*(f.failure) + (7983559872161833/100000000000000 : ℝ)*(f.sum) + (11536090873517/3557500000000000000000000000 : ℝ)*base66 + (82734227071372283/35575000000000000000000000000000 : ℝ)*base67 + (10956554329347283/35575000000000000000000000000000 : ℝ)*base69 + (385124018065797283/35575000000000000000000000000000 : ℝ)*base71 + (41956048554029/7115000000000000000000000000 : ℝ)*base74 + (748208424572952717/35575000000000000000000000000000 : ℝ)*base76 + (424872426902397283/35575000000000000000000000000000 : ℝ)*base77 + (870837893504302717/35575000000000000000000000000000 : ℝ)*base80 + (6689151127551/1778750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (721447/78125000000000000000 : ℝ)*base89 + (721447/78125000000000000000 : ℝ)*base91 + (721447/78125000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (223887651382917165814648869/35575000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1107510431/100000000000000 : ℝ)*(base19) + (1224007133/100000000000000 : ℝ)*(base23) + (15345527/12500000000000 : ℝ)*(upper3) + (2337743/5000000000000 : ℝ)*(lower4) + (16285333/12500000000000 : ℝ)*(upper5) + (2990201514613919/50000000000000 : ℝ)*(major0) + (2990201514613919/50000000000000 : ℝ)*(major1) + (2990201514613919/50000000000000 : ℝ)*(major2) + (30833923661/100000000000000 : ℝ)*(sp1) + (13321953/40000000000 : ℝ)*(sp2) + (4012361956741997/50000000000000 : ℝ)*(sp4) + (4012345986024951/50000000000000 : ℝ)*(sp5) + (4012344692297181/50000000000000 : ℝ)*(sp6) + (3936081935191723/100000000000000 : ℝ)*(sp7) + (3936081935191723/100000000000000 : ℝ)*(f.failure) + (4012361956741997/50000000000000 : ℝ)*(f.sum) + (34042832597551/7115000000000000000000000000 : ℝ)*base66 + (1020766269726185377/142300000000000000000000000000000 : ℝ)*base68 + (438778112096085377/142300000000000000000000000000000 : ℝ)*base70 + (1124380994719785377/142300000000000000000000000000000 : ℝ)*base72 + (912207376417/889375000000000000000000000 : ℝ)*base74 + (1553725923237914623/142300000000000000000000000000000 : ℝ)*base75 + (2365907686779585377/142300000000000000000000000000000 : ℝ)*base78 + (3124941155863985377/142300000000000000000000000000000 : ℝ)*base80 + (178902868063/3557500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (88614033/10000000000000000000000 : ℝ)*base89 + (88614033/10000000000000000000000 : ℝ)*base91 + (88614033/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1268_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2115/512 : ℝ) ≤ p) (hpb : p ≤ (8461/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151937971/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14239/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11393/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11487/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14141/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1268_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1268_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2115/512 : ℝ) ≤ p) (hpb : p ≤ (8461/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151937971/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4039/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9603/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11487/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14141/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1268_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1268_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1268_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2115/512 : ℝ) ≤ p) (hpb : p ≤ (8461/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151937971/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4039/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9603/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11487/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14141/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1268_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
