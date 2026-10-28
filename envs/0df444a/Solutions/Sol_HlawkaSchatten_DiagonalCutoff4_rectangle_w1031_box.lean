-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_w1031_box
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T13:38:44.582637+00:00
-- url     : https://prove2.me/submissions/1c264d61-22fc-4272-a39a-12e94a1f462b

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
theorem support_rectangle_w1031_box_0 (p : ℝ) (hpa : (8223/2048 : ℝ) ≤ p) (hpb : p ≤ (257/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-261305049/1250000000 : ℝ)*x 0 + (5377834463/10000000000 : ℝ)*x 1 + (5377834567/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (261305049/1250000000 : ℝ)^257 ≤ (12440115496759/100000000000000 : ℝ)^193 := by
    have hnat : (261305049 : ℕ)^257*100000000000000^193 ≤ 12440115496759^193*1250000000^257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      261305049 1250000000 12440115496759 100000000000000 257 193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5377834463/10000000000 : ℝ)^257 ≤ (43779941680447/100000000000000 : ℝ)^193 := by
    have hnat : (5377834463 : ℕ)^257*100000000000000^193 ≤ 43779941680447^193*10000000000^257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5377834463 10000000000 43779941680447 100000000000000 257 193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5377834567/10000000000 : ℝ)^257 ≤ (10944985701961/25000000000000 : ℝ)^193 := by
    have hnat : (5377834567 : ℕ)^257*25000000000000^193 ≤ 10944985701961^193*10000000000^257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5377834567 10000000000 10944985701961 25000000000000 257 193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (257/64 : ℝ)) 257 193 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-261305049/1250000000 : ℝ), (5377834463/10000000000 : ℝ), (5377834567/10000000000 : ℝ)] ![(12440115496759/100000000000000 : ℝ), (43779941680447/100000000000000 : ℝ), (10944985701961/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-261305049/1250000000 : ℝ)|^257 ≤ (12440115496759/100000000000000 : ℝ)^193
        have hw : |(-261305049/1250000000 : ℝ)|=(261305049/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5377834463/10000000000 : ℝ)|^257 ≤ (43779941680447/100000000000000 : ℝ)^193
        have hw : |(5377834463/10000000000 : ℝ)|=(5377834463/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5377834567/10000000000 : ℝ)|^257 ≤ (10944985701961/25000000000000 : ℝ)^193
        have hw : |(5377834567/10000000000 : ℝ)|=(5377834567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1031_box_1 (p : ℝ) (hpa : (8223/2048 : ℝ) ≤ p) (hpb : p ≤ (257/64 : ℝ)) (x : Fin 3 → ℝ) :
    (1323698147/2500000000 : ℝ)*x 0 + (-68836253/312500000 : ℝ)*x 1 + (215113369/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1323698147/2500000000 : ℝ)^257 ≤ (1715282035251/4000000000000 : ℝ)^193 := by
    have hnat : (1323698147 : ℕ)^257*4000000000000^193 ≤ 1715282035251^193*2500000000^257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1323698147 2500000000 1715282035251 4000000000000 257 193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (68836253/312500000 : ℝ)^257 ≤ (3334502501817/25000000000000 : ℝ)^193 := by
    have hnat : (68836253 : ℕ)^257*25000000000000^193 ≤ 3334502501817^193*312500000^257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      68836253 312500000 3334502501817 25000000000000 257 193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (215113369/400000000 : ℝ)^257 ≤ (21889969550221/50000000000000 : ℝ)^193 := by
    have hnat : (215113369 : ℕ)^257*50000000000000^193 ≤ 21889969550221^193*400000000^257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215113369 400000000 21889969550221 50000000000000 257 193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (257/64 : ℝ)) 257 193 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1323698147/2500000000 : ℝ), (-68836253/312500000 : ℝ), (215113369/400000000 : ℝ)] ![(1715282035251/4000000000000 : ℝ), (3334502501817/25000000000000 : ℝ), (21889969550221/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1323698147/2500000000 : ℝ)|^257 ≤ (1715282035251/4000000000000 : ℝ)^193
        have hw : |(1323698147/2500000000 : ℝ)|=(1323698147/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-68836253/312500000 : ℝ)|^257 ≤ (3334502501817/25000000000000 : ℝ)^193
        have hw : |(-68836253/312500000 : ℝ)|=(68836253/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(215113369/400000000 : ℝ)|^257 ≤ (21889969550221/50000000000000 : ℝ)^193
        have hw : |(215113369/400000000 : ℝ)|=(215113369/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1031_box_2 (p : ℝ) (hpa : (8223/2048 : ℝ) ≤ p) (hpb : p ≤ (257/64 : ℝ)) (x : Fin 3 → ℝ) :
    (529479229/1000000000 : ℝ)*x 0 + (5377834723/10000000000 : ℝ)*x 1 + (-88110393/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (529479229/1000000000 : ℝ)^257 ≤ (10720511916869/25000000000000 : ℝ)^193 := by
    have hnat : (529479229 : ℕ)^257*25000000000000^193 ≤ 10720511916869^193*1000000000^257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      529479229 1000000000 10720511916869 25000000000000 257 193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5377834723/10000000000 : ℝ)^257 ≤ (2188997224947/5000000000000 : ℝ)^193 := by
    have hnat : (5377834723 : ℕ)^257*5000000000000^193 ≤ 2188997224947^193*10000000000^257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5377834723 10000000000 2188997224947 5000000000000 257 193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (88110393/400000000 : ℝ)^257 ≤ (666900391109/5000000000000 : ℝ)^193 := by
    have hnat : (88110393 : ℕ)^257*5000000000000^193 ≤ 666900391109^193*400000000^257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      88110393 400000000 666900391109 5000000000000 257 193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (257/64 : ℝ)) 257 193 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(529479229/1000000000 : ℝ), (5377834723/10000000000 : ℝ), (-88110393/400000000 : ℝ)] ![(10720511916869/25000000000000 : ℝ), (2188997224947/5000000000000 : ℝ), (666900391109/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(529479229/1000000000 : ℝ)|^257 ≤ (10720511916869/25000000000000 : ℝ)^193
        have hw : |(529479229/1000000000 : ℝ)|=(529479229/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5377834723/10000000000 : ℝ)|^257 ≤ (2188997224947/5000000000000 : ℝ)^193
        have hw : |(5377834723/10000000000 : ℝ)|=(5377834723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-88110393/400000000 : ℝ)|^257 ≤ (666900391109/5000000000000 : ℝ)^193
        have hw : |(-88110393/400000000 : ℝ)|=(88110393/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1031_box_3 (p : ℝ) (hpa : (8223/2048 : ℝ) ≤ p) (hpb : p ≤ (257/64 : ℝ)) (x : Fin 3 → ℝ) :
    (448934371/1000000000 : ℝ)*x 0 + (2164171749/5000000000 : ℝ)*x 1 + (4328343603/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (448934371/1000000000 : ℝ)^257 ≤ (17211334054221/50000000000000 : ℝ)^193 := by
    have hnat : (448934371 : ℕ)^257*50000000000000^193 ≤ 17211334054221^193*1000000000^257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      448934371 1000000000 17211334054221 50000000000000 257 193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2164171749/5000000000 : ℝ)^257 ≤ (32788665407273/100000000000000 : ℝ)^193 := by
    have hnat : (2164171749 : ℕ)^257*100000000000000^193 ≤ 32788665407273^193*5000000000^257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2164171749 5000000000 32788665407273 100000000000000 257 193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4328343603/10000000000 : ℝ)^257 ≤ (16394333233223/50000000000000 : ℝ)^193 := by
    have hnat : (4328343603 : ℕ)^257*50000000000000^193 ≤ 16394333233223^193*10000000000^257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4328343603 10000000000 16394333233223 50000000000000 257 193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (257/64 : ℝ)) 257 193 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(448934371/1000000000 : ℝ), (2164171749/5000000000 : ℝ), (4328343603/10000000000 : ℝ)] ![(17211334054221/50000000000000 : ℝ), (32788665407273/100000000000000 : ℝ), (16394333233223/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(448934371/1000000000 : ℝ)|^257 ≤ (17211334054221/50000000000000 : ℝ)^193
        have hw : |(448934371/1000000000 : ℝ)|=(448934371/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2164171749/5000000000 : ℝ)|^257 ≤ (32788665407273/100000000000000 : ℝ)^193
        have hw : |(2164171749/5000000000 : ℝ)|=(2164171749/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4328343603/10000000000 : ℝ)|^257 ≤ (16394333233223/50000000000000 : ℝ)^193
        have hw : |(4328343603/10000000000 : ℝ)|=(4328343603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1031_box_4 (p : ℝ) (hpa : (8223/2048 : ℝ) ≤ p) (hpb : p ≤ (257/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-588297953/2500000000 : ℝ)*x 0 + (5279551171/10000000000 : ℝ)*x 1 + (659943953/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (588297953/2500000000 : ℝ)^257 ≤ (7282240141621/50000000000000 : ℝ)^193 := by
    have hnat : (588297953 : ℕ)^257*50000000000000^193 ≤ 7282240141621^193*2500000000^257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      588297953 2500000000 7282240141621 50000000000000 257 193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5279551171/10000000000 : ℝ)^257 ≤ (8543551482843/20000000000000 : ℝ)^193 := by
    have hnat : (5279551171 : ℕ)^257*20000000000000^193 ≤ 8543551482843^193*10000000000^257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5279551171 10000000000 8543551482843 20000000000000 257 193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (659943953/1250000000 : ℝ)^257 ≤ (42717762294953/100000000000000 : ℝ)^193 := by
    have hnat : (659943953 : ℕ)^257*100000000000000^193 ≤ 42717762294953^193*1250000000^257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      659943953 1250000000 42717762294953 100000000000000 257 193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (257/64 : ℝ)) 257 193 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-588297953/2500000000 : ℝ), (5279551171/10000000000 : ℝ), (659943953/1250000000 : ℝ)] ![(7282240141621/50000000000000 : ℝ), (8543551482843/20000000000000 : ℝ), (42717762294953/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-588297953/2500000000 : ℝ)|^257 ≤ (7282240141621/50000000000000 : ℝ)^193
        have hw : |(-588297953/2500000000 : ℝ)|=(588297953/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5279551171/10000000000 : ℝ)|^257 ≤ (8543551482843/20000000000000 : ℝ)^193
        have hw : |(5279551171/10000000000 : ℝ)|=(5279551171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(659943953/1250000000 : ℝ)|^257 ≤ (42717762294953/100000000000000 : ℝ)^193
        have hw : |(659943953/1250000000 : ℝ)|=(659943953/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1031_box_5 (p : ℝ) (hpa : (8223/2048 : ℝ) ≤ p) (hpb : p ≤ (257/64 : ℝ)) (x : Fin 3 → ℝ) :
    (670550677/1250000000 : ℝ)*x 0 + (-560268301/2500000000 : ℝ)*x 1 + (5279550991/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (670550677/1250000000 : ℝ)^257 ≤ (43634426330147/100000000000000 : ℝ)^193 := by
    have hnat : (670550677 : ℕ)^257*100000000000000^193 ≤ 43634426330147^193*1250000000^257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      670550677 1250000000 43634426330147 100000000000000 257 193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (560268301/2500000000 : ℝ)^257 ≤ (3411954544983/25000000000000 : ℝ)^193 := by
    have hnat : (560268301 : ℕ)^257*25000000000000^193 ≤ 3411954544983^193*2500000000^257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      560268301 2500000000 3411954544983 25000000000000 257 193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5279550991/10000000000 : ℝ)^257 ≤ (42717755474849/100000000000000 : ℝ)^193 := by
    have hnat : (5279550991 : ℕ)^257*100000000000000^193 ≤ 42717755474849^193*10000000000^257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5279550991 10000000000 42717755474849 100000000000000 257 193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (257/64 : ℝ)) 257 193 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(670550677/1250000000 : ℝ), (-560268301/2500000000 : ℝ), (5279550991/10000000000 : ℝ)] ![(43634426330147/100000000000000 : ℝ), (3411954544983/25000000000000 : ℝ), (42717755474849/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(670550677/1250000000 : ℝ)|^257 ≤ (43634426330147/100000000000000 : ℝ)^193
        have hw : |(670550677/1250000000 : ℝ)|=(670550677/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-560268301/2500000000 : ℝ)|^257 ≤ (3411954544983/25000000000000 : ℝ)^193
        have hw : |(-560268301/2500000000 : ℝ)|=(560268301/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5279550991/10000000000 : ℝ)|^257 ≤ (42717755474849/100000000000000 : ℝ)^193
        have hw : |(5279550991/10000000000 : ℝ)|=(5279550991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1031_box_6 (p : ℝ) (hpa : (8223/2048 : ℝ) ≤ p) (hpb : p ≤ (257/64 : ℝ)) (x : Fin 3 → ℝ) :
    (2682202449/5000000000 : ℝ)*x 0 + (211182069/400000000 : ℝ)*x 1 + (-1120536461/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2682202449/5000000000 : ℝ)^257 ≤ (5454302589937/12500000000000 : ℝ)^193 := by
    have hnat : (2682202449 : ℕ)^257*12500000000000^193 ≤ 5454302589937^193*5000000000^257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2682202449 5000000000 5454302589937 12500000000000 257 193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (211182069/400000000 : ℝ)^257 ≤ (2669860211447/6250000000000 : ℝ)^193 := by
    have hnat : (211182069 : ℕ)^257*6250000000000^193 ≤ 2669860211447^193*400000000^257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      211182069 400000000 2669860211447 6250000000000 257 193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1120536461/5000000000 : ℝ)^257 ≤ (13647815893111/100000000000000 : ℝ)^193 := by
    have hnat : (1120536461 : ℕ)^257*100000000000000^193 ≤ 13647815893111^193*5000000000^257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1120536461 5000000000 13647815893111 100000000000000 257 193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (257/64 : ℝ)) 257 193 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2682202449/5000000000 : ℝ), (211182069/400000000 : ℝ), (-1120536461/5000000000 : ℝ)] ![(5454302589937/12500000000000 : ℝ), (2669860211447/6250000000000 : ℝ), (13647815893111/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2682202449/5000000000 : ℝ)|^257 ≤ (5454302589937/12500000000000 : ℝ)^193
        have hw : |(2682202449/5000000000 : ℝ)|=(2682202449/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(211182069/400000000 : ℝ)|^257 ≤ (2669860211447/6250000000000 : ℝ)^193
        have hw : |(211182069/400000000 : ℝ)|=(211182069/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1120536461/5000000000 : ℝ)|^257 ≤ (13647815893111/100000000000000 : ℝ)^193
        have hw : |(-1120536461/5000000000 : ℝ)|=(1120536461/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1031_box_7 (p : ℝ) (hpa : (8223/2048 : ℝ) ≤ p) (hpb : p ≤ (257/64 : ℝ)) (x : Fin 3 → ℝ) :
    (4271445353/10000000000 : ℝ)*x 0 + (1109317671/2500000000 : ℝ)*x 1 + (4437271253/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4271445353/10000000000 : ℝ)^257 ≤ (16107983783889/50000000000000 : ℝ)^193 := by
    have hnat : (4271445353 : ℕ)^257*50000000000000^193 ≤ 16107983783889^193*10000000000^257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4271445353 10000000000 16107983783889 50000000000000 257 193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1109317671/2500000000 : ℝ)^257 ≤ (8473003328133/25000000000000 : ℝ)^193 := by
    have hnat : (1109317671 : ℕ)^257*25000000000000^193 ≤ 8473003328133^193*2500000000^257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1109317671 2500000000 8473003328133 25000000000000 257 193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4437271253/10000000000 : ℝ)^257 ≤ (16946009549873/50000000000000 : ℝ)^193 := by
    have hnat : (4437271253 : ℕ)^257*50000000000000^193 ≤ 16946009549873^193*10000000000^257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4437271253 10000000000 16946009549873 50000000000000 257 193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (257/64 : ℝ)) 257 193 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4271445353/10000000000 : ℝ), (1109317671/2500000000 : ℝ), (4437271253/10000000000 : ℝ)] ![(16107983783889/50000000000000 : ℝ), (8473003328133/25000000000000 : ℝ), (16946009549873/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4271445353/10000000000 : ℝ)|^257 ≤ (16107983783889/50000000000000 : ℝ)^193
        have hw : |(4271445353/10000000000 : ℝ)|=(4271445353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1109317671/2500000000 : ℝ)|^257 ≤ (8473003328133/25000000000000 : ℝ)^193
        have hw : |(1109317671/2500000000 : ℝ)|=(1109317671/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4437271253/10000000000 : ℝ)|^257 ≤ (16946009549873/50000000000000 : ℝ)^193
        have hw : |(4437271253/10000000000 : ℝ)|=(4437271253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1031_box_8 (p : ℝ) (hpa : (8223/2048 : ℝ) ≤ p) (hpb : p ≤ (257/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-1149192699/5000000000 : ℝ)*x 0 + (651616279/1250000000 : ℝ)*x 1 + (2693714859/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1149192699/5000000000 : ℝ)^257 ≤ (14114539120069/100000000000000 : ℝ)^193 := by
    have hnat : (1149192699 : ℕ)^257*100000000000000^193 ≤ 14114539120069^193*5000000000^257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1149192699 5000000000 14114539120069 100000000000000 257 193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (651616279/1250000000 : ℝ)^257 ≤ (8400294487451/20000000000000 : ℝ)^193 := by
    have hnat : (651616279 : ℕ)^257*20000000000000^193 ≤ 8400294487451^193*1250000000^257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      651616279 1250000000 8400294487451 20000000000000 257 193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2693714859/5000000000 : ℝ)^257 ≤ (43883988423741/100000000000000 : ℝ)^193 := by
    have hnat : (2693714859 : ℕ)^257*100000000000000^193 ≤ 43883988423741^193*5000000000^257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2693714859 5000000000 43883988423741 100000000000000 257 193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (257/64 : ℝ)) 257 193 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1149192699/5000000000 : ℝ), (651616279/1250000000 : ℝ), (2693714859/5000000000 : ℝ)] ![(14114539120069/100000000000000 : ℝ), (8400294487451/20000000000000 : ℝ), (43883988423741/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1149192699/5000000000 : ℝ)|^257 ≤ (14114539120069/100000000000000 : ℝ)^193
        have hw : |(-1149192699/5000000000 : ℝ)|=(1149192699/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(651616279/1250000000 : ℝ)|^257 ≤ (8400294487451/20000000000000 : ℝ)^193
        have hw : |(651616279/1250000000 : ℝ)|=(651616279/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2693714859/5000000000 : ℝ)|^257 ≤ (43883988423741/100000000000000 : ℝ)^193
        have hw : |(2693714859/5000000000 : ℝ)|=(2693714859/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1031_box_9 (p : ℝ) (hpa : (8223/2048 : ℝ) ≤ p) (hpb : p ≤ (257/64 : ℝ)) (x : Fin 3 → ℝ) :
    (42303937/80000000 : ℝ)*x 0 + (-2198948661/10000000000 : ℝ)*x 1 + (5387429537/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (42303937/80000000 : ℝ)^257 ≤ (5351090813247/12500000000000 : ℝ)^193 := by
    have hnat : (42303937 : ℕ)^257*12500000000000^193 ≤ 5351090813247^193*80000000^257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42303937 80000000 5351090813247 12500000000000 257 193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2198948661/10000000000 : ℝ)^257 ≤ (13307287015093/100000000000000 : ℝ)^193 := by
    have hnat : (2198948661 : ℕ)^257*100000000000000^193 ≤ 13307287015093^193*10000000000^257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2198948661 10000000000 13307287015093 100000000000000 257 193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5387429537/10000000000 : ℝ)^257 ≤ (43883986460477/100000000000000 : ℝ)^193 := by
    have hnat : (5387429537 : ℕ)^257*100000000000000^193 ≤ 43883986460477^193*10000000000^257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5387429537 10000000000 43883986460477 100000000000000 257 193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (257/64 : ℝ)) 257 193 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(42303937/80000000 : ℝ), (-2198948661/10000000000 : ℝ), (5387429537/10000000000 : ℝ)] ![(5351090813247/12500000000000 : ℝ), (13307287015093/100000000000000 : ℝ), (43883986460477/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(42303937/80000000 : ℝ)|^257 ≤ (5351090813247/12500000000000 : ℝ)^193
        have hw : |(42303937/80000000 : ℝ)|=(42303937/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2198948661/10000000000 : ℝ)|^257 ≤ (13307287015093/100000000000000 : ℝ)^193
        have hw : |(-2198948661/10000000000 : ℝ)|=(2198948661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5387429537/10000000000 : ℝ)|^257 ≤ (43883986460477/100000000000000 : ℝ)^193
        have hw : |(5387429537/10000000000 : ℝ)|=(5387429537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1031_box_10 (p : ℝ) (hpa : (8223/2048 : ℝ) ≤ p) (hpb : p ≤ (257/64 : ℝ)) (x : Fin 3 → ℝ) :
    (5287992491/10000000000 : ℝ)*x 0 + (5387429683/10000000000 : ℝ)*x 1 + (-274868497/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5287992491/10000000000 : ℝ)^257 ≤ (42808730451443/100000000000000 : ℝ)^193 := by
    have hnat : (5287992491 : ℕ)^257*100000000000000^193 ≤ 42808730451443^193*10000000000^257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5287992491 10000000000 42808730451443 100000000000000 257 193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5387429683/10000000000 : ℝ)^257 ≤ (8776797608821/20000000000000 : ℝ)^193 := by
    have hnat : (5387429683 : ℕ)^257*20000000000000^193 ≤ 8776797608821^193*10000000000^257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5387429683 10000000000 8776797608821 20000000000000 257 193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (274868497/1250000000 : ℝ)^257 ≤ (13307281495071/100000000000000 : ℝ)^193 := by
    have hnat : (274868497 : ℕ)^257*100000000000000^193 ≤ 13307281495071^193*1250000000^257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      274868497 1250000000 13307281495071 100000000000000 257 193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (257/64 : ℝ)) 257 193 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5287992491/10000000000 : ℝ), (5387429683/10000000000 : ℝ), (-274868497/1250000000 : ℝ)] ![(42808730451443/100000000000000 : ℝ), (8776797608821/20000000000000 : ℝ), (13307281495071/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5287992491/10000000000 : ℝ)|^257 ≤ (42808730451443/100000000000000 : ℝ)^193
        have hw : |(5287992491/10000000000 : ℝ)|=(5287992491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5387429683/10000000000 : ℝ)|^257 ≤ (8776797608821/20000000000000 : ℝ)^193
        have hw : |(5387429683/10000000000 : ℝ)|=(5387429683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-274868497/1250000000 : ℝ)|^257 ≤ (13307281495071/100000000000000 : ℝ)^193
        have hw : |(-274868497/1250000000 : ℝ)|=(274868497/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1031_box_11 (p : ℝ) (hpa : (8223/2048 : ℝ) ≤ p) (hpb : p ≤ (257/64 : ℝ)) (x : Fin 3 → ℝ) :
    (225517153/500000000 : ℝ)*x 0 + (4317703393/10000000000 : ℝ)*x 1 + (4317703347/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (225517153/500000000 : ℝ)^257 ≤ (34637243384609/100000000000000 : ℝ)^193 := by
    have hnat : (225517153 : ℕ)^257*100000000000000^193 ≤ 34637243384609^193*500000000^257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      225517153 500000000 34637243384609 100000000000000 257 193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4317703393/10000000000 : ℝ)^257 ≤ (6536275706019/20000000000000 : ℝ)^193 := by
    have hnat : (4317703393 : ℕ)^257*20000000000000^193 ≤ 6536275706019^193*10000000000^257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4317703393 10000000000 6536275706019 20000000000000 257 193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4317703347/10000000000 : ℝ)^257 ≤ (16340689033227/50000000000000 : ℝ)^193 := by
    have hnat : (4317703347 : ℕ)^257*50000000000000^193 ≤ 16340689033227^193*10000000000^257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4317703347 10000000000 16340689033227 50000000000000 257 193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (257/64 : ℝ)) 257 193 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(225517153/500000000 : ℝ), (4317703393/10000000000 : ℝ), (4317703347/10000000000 : ℝ)] ![(34637243384609/100000000000000 : ℝ), (6536275706019/20000000000000 : ℝ), (16340689033227/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(225517153/500000000 : ℝ)|^257 ≤ (34637243384609/100000000000000 : ℝ)^193
        have hw : |(225517153/500000000 : ℝ)|=(225517153/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4317703393/10000000000 : ℝ)|^257 ≤ (6536275706019/20000000000000 : ℝ)^193
        have hw : |(4317703393/10000000000 : ℝ)|=(4317703393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4317703347/10000000000 : ℝ)|^257 ≤ (16340689033227/50000000000000 : ℝ)^193
        have hw : |(4317703347/10000000000 : ℝ)|=(4317703347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1031_box_12 (p : ℝ) (hpa : (8223/2048 : ℝ) ≤ p) (hpb : p ≤ (257/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-2145639187/10000000000 : ℝ)*x 0 + (5443092239/10000000000 : ℝ)*x 1 + (527157007/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2145639187/10000000000 : ℝ)^257 ≤ (2575886547763/20000000000000 : ℝ)^193 := by
    have hnat : (2145639187 : ℕ)^257*20000000000000^193 ≤ 2575886547763^193*10000000000^257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2145639187 10000000000 2575886547763 20000000000000 257 193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5443092239/10000000000 : ℝ)^257 ≤ (355910229561/800000000000 : ℝ)^193 := by
    have hnat : (5443092239 : ℕ)^257*800000000000^193 ≤ 355910229561^193*10000000000^257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5443092239 10000000000 355910229561 800000000000 257 193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (527157007/1000000000 : ℝ)^257 ≤ (8526357711199/20000000000000 : ℝ)^193 := by
    have hnat : (527157007 : ℕ)^257*20000000000000^193 ≤ 8526357711199^193*1000000000^257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      527157007 1000000000 8526357711199 20000000000000 257 193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (257/64 : ℝ)) 257 193 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2145639187/10000000000 : ℝ), (5443092239/10000000000 : ℝ), (527157007/1000000000 : ℝ)] ![(2575886547763/20000000000000 : ℝ), (355910229561/800000000000 : ℝ), (8526357711199/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2145639187/10000000000 : ℝ)|^257 ≤ (2575886547763/20000000000000 : ℝ)^193
        have hw : |(-2145639187/10000000000 : ℝ)|=(2145639187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5443092239/10000000000 : ℝ)|^257 ≤ (355910229561/800000000000 : ℝ)^193
        have hw : |(5443092239/10000000000 : ℝ)|=(5443092239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(527157007/1000000000 : ℝ)|^257 ≤ (8526357711199/20000000000000 : ℝ)^193
        have hw : |(527157007/1000000000 : ℝ)|=(527157007/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1031_box_13 (p : ℝ) (hpa : (8223/2048 : ℝ) ≤ p) (hpb : p ≤ (257/64 : ℝ)) (x : Fin 3 → ℝ) :
    (5370055679/10000000000 : ℝ)*x 0 + (-2244125029/10000000000 : ℝ)*x 1 + (5271570293/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5370055679/10000000000 : ℝ)^257 ≤ (43695637118911/100000000000000 : ℝ)^193 := by
    have hnat : (5370055679 : ℕ)^257*100000000000000^193 ≤ 43695637118911^193*10000000000^257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5370055679 10000000000 43695637118911 100000000000000 257 193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2244125029/10000000000 : ℝ)^257 ≤ (1367257190953/10000000000000 : ℝ)^193 := by
    have hnat : (2244125029 : ℕ)^257*10000000000000^193 ≤ 1367257190953^193*10000000000^257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2244125029 10000000000 1367257190953 10000000000000 257 193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5271570293/10000000000 : ℝ)^257 ≤ (5328973869681/12500000000000 : ℝ)^193 := by
    have hnat : (5271570293 : ℕ)^257*12500000000000^193 ≤ 5328973869681^193*10000000000^257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5271570293 10000000000 5328973869681 12500000000000 257 193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (257/64 : ℝ)) 257 193 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5370055679/10000000000 : ℝ), (-2244125029/10000000000 : ℝ), (5271570293/10000000000 : ℝ)] ![(43695637118911/100000000000000 : ℝ), (1367257190953/10000000000000 : ℝ), (5328973869681/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5370055679/10000000000 : ℝ)|^257 ≤ (43695637118911/100000000000000 : ℝ)^193
        have hw : |(5370055679/10000000000 : ℝ)|=(5370055679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2244125029/10000000000 : ℝ)|^257 ≤ (1367257190953/10000000000000 : ℝ)^193
        have hw : |(-2244125029/10000000000 : ℝ)|=(2244125029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5271570293/10000000000 : ℝ)|^257 ≤ (5328973869681/12500000000000 : ℝ)^193
        have hw : |(5271570293/10000000000 : ℝ)|=(5271570293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1031_box_14 (p : ℝ) (hpa : (8223/2048 : ℝ) ≤ p) (hpb : p ≤ (257/64 : ℝ)) (x : Fin 3 → ℝ) :
    (83907123/156250000 : ℝ)*x 0 + (5271570223/10000000000 : ℝ)*x 1 + (-35064451/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (83907123/156250000 : ℝ)^257 ≤ (2730977450631/6250000000000 : ℝ)^193 := by
    have hnat : (83907123 : ℕ)^257*6250000000000^193 ≤ 2730977450631^193*156250000^257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      83907123 156250000 2730977450631 6250000000000 257 193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5271570223/10000000000 : ℝ)^257 ≤ (42631790203629/100000000000000 : ℝ)^193 := by
    have hnat : (5271570223 : ℕ)^257*100000000000000^193 ≤ 42631790203629^193*10000000000^257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5271570223 10000000000 42631790203629 100000000000000 257 193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (35064451/156250000 : ℝ)^257 ≤ (13672570570893/100000000000000 : ℝ)^193 := by
    have hnat : (35064451 : ℕ)^257*100000000000000^193 ≤ 13672570570893^193*156250000^257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      35064451 156250000 13672570570893 100000000000000 257 193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (257/64 : ℝ)) 257 193 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(83907123/156250000 : ℝ), (5271570223/10000000000 : ℝ), (-35064451/156250000 : ℝ)] ![(2730977450631/6250000000000 : ℝ), (42631790203629/100000000000000 : ℝ), (13672570570893/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(83907123/156250000 : ℝ)|^257 ≤ (2730977450631/6250000000000 : ℝ)^193
        have hw : |(83907123/156250000 : ℝ)|=(83907123/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5271570223/10000000000 : ℝ)|^257 ≤ (42631790203629/100000000000000 : ℝ)^193
        have hw : |(5271570223/10000000000 : ℝ)|=(5271570223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-35064451/156250000 : ℝ)|^257 ≤ (13672570570893/100000000000000 : ℝ)^193
        have hw : |(-35064451/156250000 : ℝ)|=(35064451/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1031_box_15 (p : ℝ) (hpa : (8223/2048 : ℝ) ≤ p) (hpb : p ≤ (257/64 : ℝ)) (x : Fin 3 → ℝ) :
    (4253520791/10000000000 : ℝ)*x 0 + (4446111619/10000000000 : ℝ)*x 1 + (555763969/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4253520791/10000000000 : ℝ)^257 ≤ (6407214593031/20000000000000 : ℝ)^193 := by
    have hnat : (4253520791 : ℕ)^257*20000000000000^193 ≤ 6407214593031^193*10000000000^257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4253520791 10000000000 6407214593031 20000000000000 257 193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4446111619/10000000000 : ℝ)^257 ≤ (33981962830387/100000000000000 : ℝ)^193 := by
    have hnat : (4446111619 : ℕ)^257*100000000000000^193 ≤ 33981962830387^193*10000000000^257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4446111619 10000000000 33981962830387 100000000000000 257 193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (555763969/1250000000 : ℝ)^257 ≤ (33981964184003/100000000000000 : ℝ)^193 := by
    have hnat : (555763969 : ℕ)^257*100000000000000^193 ≤ 33981964184003^193*1250000000^257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      555763969 1250000000 33981964184003 100000000000000 257 193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (257/64 : ℝ)) 257 193 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4253520791/10000000000 : ℝ), (4446111619/10000000000 : ℝ), (555763969/1250000000 : ℝ)] ![(6407214593031/20000000000000 : ℝ), (33981962830387/100000000000000 : ℝ), (33981964184003/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4253520791/10000000000 : ℝ)|^257 ≤ (6407214593031/20000000000000 : ℝ)^193
        have hw : |(4253520791/10000000000 : ℝ)|=(4253520791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4446111619/10000000000 : ℝ)|^257 ≤ (33981962830387/100000000000000 : ℝ)^193
        have hw : |(4446111619/10000000000 : ℝ)|=(4446111619/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(555763969/1250000000 : ℝ)|^257 ≤ (33981964184003/100000000000000 : ℝ)^193
        have hw : |(555763969/1250000000 : ℝ)|=(555763969/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1031_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8223/2048 : ℝ) ≤ p) (hpb : p ≤ (257/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73656321/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (699/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11203/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(62223/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(11843/20000 : ℝ) ∧ (79461/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (10359/12500 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (699/5000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11203/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (699/5000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11203/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (699/5000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11203/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (699/5000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11203/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (699/5000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11203/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (699/5000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11203/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11203/100000 : ℝ) ^ (8223/2048 : ℝ) ≤ (15238681255830173/100000000000000000000 : ℝ) := by
    have hpowers : (11203/100000 : ℝ)^8223 ≤ (15238681255830173/100000000000000000000 : ℝ)^2048 := by
      have hnat : (11203 : ℕ)^8223*100000000000000000000^2048 ≤ 15238681255830173^2048*100000^8223 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11203 100000 15238681255830173 100000000000000000000 8223 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11203/100000 : ℝ)) (X := (15238681255830173/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8223 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (699/5000 : ℝ) ^ (8223/2048 : ℝ) ≤ (18538068063225657/50000000000000000000 : ℝ) := by
    have hpowers : (699/5000 : ℝ)^8223 ≤ (18538068063225657/50000000000000000000 : ℝ)^2048 := by
      have hnat : (699 : ℕ)^8223*50000000000000000000^2048 ≤ 18538068063225657^2048*5000^8223 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        699 5000 18538068063225657 50000000000000000000 8223 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (699/5000 : ℝ)) (X := (18538068063225657/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8223 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50015238681255830173/50000000000000000000 : ℝ) ≤ (2500189743697589/2500000000000000 : ℝ) ^ (8223/2048 : ℝ) := by
    have hpowers : (50015238681255830173/50000000000000000000 : ℝ)^2048 ≤ (2500189743697589/2500000000000000 : ℝ)^8223 := by
      have hnat : (50015238681255830173 : ℕ)^2048*2500000000000000^8223 ≤ 2500189743697589^8223*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50015238681255830173 50000000000000000000 2500189743697589 2500000000000000 2048 8223 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500189743697589/2500000000000000 : ℝ)) (X := (50015238681255830173/50000000000000000000 : ℝ)) (by norm_num) 8223 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100052314817382281487/100000000000000000000 : ℝ) ≤ (10001302684021369/10000000000000000 : ℝ) ^ (8223/2048 : ℝ) := by
    have hpowers : (100052314817382281487/100000000000000000000 : ℝ)^2048 ≤ (10001302684021369/10000000000000000 : ℝ)^8223 := by
      have hnat : (100052314817382281487 : ℕ)^2048*10000000000000000^8223 ≤ 10001302684021369^8223*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100052314817382281487 100000000000000000000 10001302684021369 10000000000000000 2048 8223 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001302684021369/10000000000000000 : ℝ)) (X := (100052314817382281487/100000000000000000000 : ℝ)) (by norm_num) 8223 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25018538068063225657/25000000000000000000 : ℝ) ≤ (5000923196626191/5000000000000000 : ℝ) ^ (8223/2048 : ℝ) := by
    have hpowers : (25018538068063225657/25000000000000000000 : ℝ)^2048 ≤ (5000923196626191/5000000000000000 : ℝ)^8223 := by
      have hnat : (25018538068063225657 : ℕ)^2048*5000000000000000^8223 ≤ 5000923196626191^8223*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25018538068063225657 25000000000000000000 5000923196626191 5000000000000000 2048 8223 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000923196626191/5000000000000000 : ℝ)) (X := (25018538068063225657/25000000000000000000 : ℝ)) (by norm_num) 8223 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(15238681255830173/100000000000000000000 : ℝ) ≤ ((13879962661981370667/13885000000000000000 : ℝ)+2*(543709231013/277700000000000 : ℝ)*(11203/100000 : ℝ))^(8223/2048 : ℝ) := by
    rw [show (13879962661981370667/13885000000000000000 : ℝ)+2*(543709231013/277700000000000 : ℝ)*(11203/100000 : ℝ)=(2500189743697589/2500000000000000 : ℝ) by norm_num, show 1+2*(15238681255830173/100000000000000000000 : ℝ)=(50015238681255830173/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(18538068063225657/50000000000000000000 : ℝ)+(15238681255830173/100000000000000000000 : ℝ) ≤ ((13879962661981370667/13885000000000000000 : ℝ)+(543709231013/277700000000000 : ℝ)*((699/5000 : ℝ)+(11203/100000 : ℝ)))^(8223/2048 : ℝ) := by
    rw [show (13879962661981370667/13885000000000000000 : ℝ)+(543709231013/277700000000000 : ℝ)*((699/5000 : ℝ)+(11203/100000 : ℝ))=(10001302684021369/10000000000000000 : ℝ) by norm_num, show 1+(18538068063225657/50000000000000000000 : ℝ)+(15238681255830173/100000000000000000000 : ℝ)=(100052314817382281487/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(18538068063225657/50000000000000000000 : ℝ) ≤ ((13879962661981370667/13885000000000000000 : ℝ)+2*(543709231013/277700000000000 : ℝ)*(699/5000 : ℝ))^(8223/2048 : ℝ) := by
    rw [show (13879962661981370667/13885000000000000000 : ℝ)+2*(543709231013/277700000000000 : ℝ)*(699/5000 : ℝ)=(5000923196626191/5000000000000000 : ℝ) by norm_num, show 1+2*(18538068063225657/50000000000000000000 : ℝ)=(25018538068063225657/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13879962661981370667/13885000000000000000 : ℝ)*(X 1 0+X 2 0)+(543709231013/277700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8223/2048 : ℝ)) (lo := (11203/100000 : ℝ)) (hi := (699/5000 : ℝ)) (c := (13879962661981370667/13885000000000000000 : ℝ)) (alpha := (543709231013/277700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13879962661981370667/13885000000000000000 : ℝ)*(X 0 1+X 2 1)+(543709231013/277700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8223/2048 : ℝ)) (lo := (11203/100000 : ℝ)) (hi := (699/5000 : ℝ)) (c := (13879962661981370667/13885000000000000000 : ℝ)) (alpha := (543709231013/277700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13879962661981370667/13885000000000000000 : ℝ)*(X 0 2+X 1 2)+(543709231013/277700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8223/2048 : ℝ)) (lo := (11203/100000 : ℝ)) (hi := (699/5000 : ℝ)) (c := (13879962661981370667/13885000000000000000 : ℝ)) (alpha := (543709231013/277700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-261305049/1250000000 : ℝ)*X 0 0+(5377834463/10000000000 : ℝ)*X 0 1+(5377834567/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1031_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1323698147/2500000000 : ℝ)*X 1 0+(-68836253/312500000 : ℝ)*X 1 1+(215113369/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1031_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((529479229/1000000000 : ℝ)*X 2 0+(5377834723/10000000000 : ℝ)*X 2 1+(-88110393/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1031_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((448934371/1000000000 : ℝ)*X 0 0+(2164171749/5000000000 : ℝ)*X 0 1+(4328343603/10000000000 : ℝ)*X 0 2+(448934371/1000000000 : ℝ)*X 1 0+(2164171749/5000000000 : ℝ)*X 1 1+(4328343603/10000000000 : ℝ)*X 1 2+(448934371/1000000000 : ℝ)*X 2 0+(2164171749/5000000000 : ℝ)*X 2 1+(4328343603/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1031_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-588297953/2500000000 : ℝ)*X 0 0+(5279551171/10000000000 : ℝ)*X 0 1+(659943953/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1031_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((670550677/1250000000 : ℝ)*X 1 0+(-560268301/2500000000 : ℝ)*X 1 1+(5279550991/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1031_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2682202449/5000000000 : ℝ)*X 2 0+(211182069/400000000 : ℝ)*X 2 1+(-1120536461/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1031_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4271445353/10000000000 : ℝ)*X 0 0+(1109317671/2500000000 : ℝ)*X 0 1+(4437271253/10000000000 : ℝ)*X 0 2+(4271445353/10000000000 : ℝ)*X 1 0+(1109317671/2500000000 : ℝ)*X 1 1+(4437271253/10000000000 : ℝ)*X 1 2+(4271445353/10000000000 : ℝ)*X 2 0+(1109317671/2500000000 : ℝ)*X 2 1+(4437271253/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1031_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1149192699/5000000000 : ℝ)*X 0 0+(651616279/1250000000 : ℝ)*X 0 1+(2693714859/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1031_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((42303937/80000000 : ℝ)*X 1 0+(-2198948661/10000000000 : ℝ)*X 1 1+(5387429537/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1031_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5287992491/10000000000 : ℝ)*X 2 0+(5387429683/10000000000 : ℝ)*X 2 1+(-274868497/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1031_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((225517153/500000000 : ℝ)*X 0 0+(4317703393/10000000000 : ℝ)*X 0 1+(4317703347/10000000000 : ℝ)*X 0 2+(225517153/500000000 : ℝ)*X 1 0+(4317703393/10000000000 : ℝ)*X 1 1+(4317703347/10000000000 : ℝ)*X 1 2+(225517153/500000000 : ℝ)*X 2 0+(4317703393/10000000000 : ℝ)*X 2 1+(4317703347/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1031_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-2145639187/10000000000 : ℝ)*X 0 0+(5443092239/10000000000 : ℝ)*X 0 1+(527157007/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1031_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5370055679/10000000000 : ℝ)*X 1 0+(-2244125029/10000000000 : ℝ)*X 1 1+(5271570293/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1031_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((83907123/156250000 : ℝ)*X 2 0+(5271570223/10000000000 : ℝ)*X 2 1+(-35064451/156250000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1031_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((4253520791/10000000000 : ℝ)*X 0 0+(4446111619/10000000000 : ℝ)*X 0 1+(555763969/1250000000 : ℝ)*X 0 2+(4253520791/10000000000 : ℝ)*X 1 0+(4446111619/10000000000 : ℝ)*X 1 1+(555763969/1250000000 : ℝ)*X 1 2+(4253520791/10000000000 : ℝ)*X 2 0+(4446111619/10000000000 : ℝ)*X 2 1+(555763969/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1031_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-62223/100000 : ℝ) ≤ (-2159833587490054288451242953/3471250000000000000000000000 : ℝ) := by norm_num
    linear_combination (112858951/100000000000000 : ℝ)*(upper1) + (1187547/2000000000000 : ℝ)*(upper2) + (103869269/100000000000000 : ℝ)*(lower4) + (174476431/50000000000000 : ℝ)*(upper5) + (3826988223849303/100000000000000 : ℝ)*(major0) + (3826988223849303/100000000000000 : ℝ)*(major1) + (3826988223849303/100000000000000 : ℝ)*(major2) + (4242952739/20000000000000 : ℝ)*(sp1) + (3443904631/50000000000000 : ℝ)*(sp2) + (2402426167/12500000000000 : ℝ)*(sp3) + (5076848496259153/100000000000000 : ℝ)*(sp4) + (2538413640747729/50000000000000 : ℝ)*(sp5) + (5076841608449891/100000000000000 : ℝ)*(sp6) + (259784894172873/10000000000000 : ℝ)*(sp7) + (1298934080569033/50000000000000 : ℝ)*(f.failure) + (5076848496259153/100000000000000 : ℝ)*(f.sum) + (29963209834549/13885000000000000000000000000 : ℝ)*base65 + (15043009746583954899/1388500000000000000000000000000000 : ℝ)*base68 + (2507248463655454899/1388500000000000000000000000000000 : ℝ)*base70 + (9061635413826545101/1388500000000000000000000000000000 : ℝ)*base71 + (18350997136979/13885000000000000000000000000 : ℝ)*base73 + (2549188419426045101/1388500000000000000000000000000000 : ℝ)*base75 + (10500034063291545101/1388500000000000000000000000000000 : ℝ)*base77 + (2336982650046954899/1388500000000000000000000000000000 : ℝ)*base80 + (31054598060771/13885000000000000000000000000 : ℝ)*base82 + (17692407/2500000000000000000000 : ℝ)*base90 + (17692407/2500000000000000000000 : ℝ)*base92 + (17692407/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (11843/20000 : ℝ) ≤ (6423704432076170491248556937589/10847656250000000000000000000000 : ℝ) := by norm_num
    linear_combination (2189969/100000000000000 : ℝ)*(upper0) + (199007/5000000000000 : ℝ)*(lower3) + (18583389/100000000000000 : ℝ)*(upper4) + (64864351/100000000000000 : ℝ)*(upper5) + (121541036605411/3125000000000 : ℝ)*(major0) + (121541036605411/3125000000000 : ℝ)*(major1) + (121541036605411/3125000000000 : ℝ)*(major2) + (639838886546059/12500000000000 : ℝ)*(sp0) + (639816599649587/12500000000000 : ℝ)*(sp1) + (5118703928147981/100000000000000 : ℝ)*(sp2) + (660042942167851/25000000000000 : ℝ)*(sp3) + (1791055123/25000000000000 : ℝ)*(sp6) + (2785862059/1562500000000 : ℝ)*(sp9) + (4334729927/100000000000000 : ℝ)*(sp11) + (264017610340133/10000000000000 : ℝ)*(f.failure) + (639838886546059/12500000000000 : ℝ)*(f.sum) + (24937918532721/3471250000000000000000000000 : ℝ)*base66 + (23190049960647381/21695312500000000000000000000000 : ℝ)*base67 + (16965266471230891/1355957031250000000000000000000 : ℝ)*base69 + (119126449674216637/43390625000000000000000000000000 : ℝ)*base71 + (123386741905341/13885000000000000000000000000 : ℝ)*base73 + (13064261553227407/2711914062500000000000000000000 : ℝ)*base75 + (65084161360685387/43390625000000000000000000000000 : ℝ)*base77 + (1646484762752113/43390625000000000000000000000000 : ℝ)*base80 + (4935280962039/3471250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (4569307/500000000000000000000 : ℝ)*base90 + (4569307/500000000000000000000 : ℝ)*base92 + (4569307/500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (79461/100000 : ℝ) ≤ (551677815963099065261647662391749/694250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (167904441/100000000000000 : ℝ)*(upper0) + (77354039/100000000000000 : ℝ)*(lower3) + (224107301/50000000000000 : ℝ)*(upper4) + (4357634718303749/100000000000000 : ℝ)*(major0) + (4357634718303749/100000000000000 : ℝ)*(major1) + (4357634718303749/100000000000000 : ℝ)*(major2) + (43738634459/50000000000000 : ℝ)*(sp1) + (6846703811/1562500000000 : ℝ)*(sp2) + (17806966539/10000000000000 : ℝ)*(sp3) + (5112655949/50000000000000 : ℝ)*(sp4) + (2865342602913391/50000000000000 : ℝ)*(sp8) + (2865303976934881/50000000000000 : ℝ)*(sp9) + (716282155261847/12500000000000 : ℝ)*(sp10) + (118316319360427/4000000000000 : ℝ)*(sp11) + (92440189177377/3125000000000 : ℝ)*(f.failure) + (143267385778467/2500000000000 : ℝ)*(f.sum) + (2859553655643/13885000000000000000000000000 : ℝ)*base66 + (10458241477662919417/1388500000000000000000000000000000 : ℝ)*base68 + (19196070236483919417/1388500000000000000000000000000000 : ℝ)*base70 + (5124330351042580583/1388500000000000000000000000000000 : ℝ)*base71 + (78322787826061/1735625000000000000000000000 : ℝ)*base74 + (1006093906349919417/1388500000000000000000000000000000 : ℝ)*base76 + (5501692518375580583/1388500000000000000000000000000000 : ℝ)*base77 + (134111259793755919417/1388500000000000000000000000000000 : ℝ)*base80 + (7976868344039/6942500000000000000000000000 : ℝ)*base82 + (1562483/156250000000000000000 : ℝ)*base90 + (1562483/156250000000000000000 : ℝ)*base92 + (1562483/156250000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (-10359/12500 : ℝ) ≤ (-1150644382014760325266694421/1388500000000000000000000000 : ℝ) := by norm_num
    linear_combination (1052787/4000000000000 : ℝ)*(lower1) + (11682309/12500000000000 : ℝ)*(lower2) + (59915143/50000000000000 : ℝ)*(upper5) + (219598069490597/5000000000000 : ℝ)*(major0) + (219598069490597/5000000000000 : ℝ)*(major1) + (219598069490597/5000000000000 : ℝ)*(major2) + (4634184193/100000000000000 : ℝ)*(sp0) + (6747006183/20000000000000 : ℝ)*(sp6) + (5960767449/6250000000000 : ℝ)*(sp7) + (4699472531/100000000000000 : ℝ)*(sp8) + (5830148673639199/100000000000000 : ℝ)*(sp12) + (5830158007295923/100000000000000 : ℝ)*(sp13) + (364382767016563/6250000000000 : ℝ)*(sp14) + (2981292599713023/100000000000000 : ℝ)*(sp15) + (1490693985996103/50000000000000 : ℝ)*(f.failure) + (5830158007295923/100000000000000 : ℝ)*(f.sum) + (9504540129609/1388500000000000000000000000 : ℝ)*base65 + (704202318009043199/69425000000000000000000000000000 : ℝ)*base67 + (68425748180306801/69425000000000000000000000000000 : ℝ)*base70 + (171639645403181801/69425000000000000000000000000000 : ℝ)*base72 + (1172813405371/1388500000000000000000000000 : ℝ)*base73 + (77115385233806801/69425000000000000000000000000000 : ℝ)*base76 + (326953214425993199/69425000000000000000000000000000 : ℝ)*base77 + (642937668096068199/69425000000000000000000000000000 : ℝ)*base79 + (928406393859/1388500000000000000000000000 : ℝ)*base82 + (32682937/2500000000000000000000 : ℝ)*base90 + (32682937/2500000000000000000000 : ℝ)*base92 + (32682937/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1031_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8223/2048 : ℝ) ≤ p) (hpb : p ≤ (257/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73656321/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (699/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11203/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62223/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(11843/20000 : ℝ) else (79461/100000 : ℝ) ≤ X j i ∧ X j i ≤ (10359/12500 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1031_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8223/2048 : ℝ) ≤ p) (hpb : p ≤ (257/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73656321/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (699/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11203/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62223/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(11843/20000 : ℝ) else (79461/100000 : ℝ) ≤ X j i ∧ X j i ≤ (10359/12500 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_w1031_box p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
