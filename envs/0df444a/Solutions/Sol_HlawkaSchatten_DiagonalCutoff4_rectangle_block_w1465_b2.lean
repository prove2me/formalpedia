-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1465_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:08:45.715543+00:00
-- url     : https://prove2.me/submissions/0edda928-dbbc-45e2-ba9c-b684b1e19882

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
theorem support_rectangle_w1465_s6_0 (p : ℝ) (hpa : (4425/1024 : ℝ) ≤ p) (hpb : p ≤ (4427/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-77590101/400000000 : ℝ)*x 0 + (42495439/78125000 : ℝ)*x 1 + (1303722007/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (77590101/400000000 : ℝ)^4427 ≤ (2960474993489/25000000000000 : ℝ)^3403 := by
    have hnat : (77590101 : ℕ)^4427*25000000000000^3403 ≤ 2960474993489^3403*400000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      77590101 400000000 2960474993489 25000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (42495439/78125000 : ℝ)^4427 ≤ (45287367366983/100000000000000 : ℝ)^3403 := by
    have hnat : (42495439 : ℕ)^4427*100000000000000^3403 ≤ 45287367366983^3403*78125000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42495439 78125000 45287367366983 100000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1303722007/2500000000 : ℝ)^4427 ≤ (21435366320139/50000000000000 : ℝ)^3403 := by
    have hnat : (1303722007 : ℕ)^4427*50000000000000^3403 ≤ 21435366320139^3403*2500000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1303722007 2500000000 21435366320139 50000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4427/1024 : ℝ)) 4427 3403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-77590101/400000000 : ℝ), (42495439/78125000 : ℝ), (1303722007/2500000000 : ℝ)] ![(2960474993489/25000000000000 : ℝ), (45287367366983/100000000000000 : ℝ), (21435366320139/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-77590101/400000000 : ℝ)|^4427 ≤ (2960474993489/25000000000000 : ℝ)^3403
        have hw : |(-77590101/400000000 : ℝ)|=(77590101/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(42495439/78125000 : ℝ)|^4427 ≤ (45287367366983/100000000000000 : ℝ)^3403
        have hw : |(42495439/78125000 : ℝ)|=(42495439/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1303722007/2500000000 : ℝ)|^4427 ≤ (21435366320139/50000000000000 : ℝ)^3403
        have hw : |(1303722007/2500000000 : ℝ)|=(1303722007/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1465_s6_1 (p : ℝ) (hpa : (4425/1024 : ℝ) ≤ p) (hpb : p ≤ (4427/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5354068187/10000000000 : ℝ)*x 0 + (-410972047/2000000000 : ℝ)*x 1 + (1303722007/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5354068187/10000000000 : ℝ)^4427 ≤ (11091286341523/25000000000000 : ℝ)^3403 := by
    have hnat : (5354068187 : ℕ)^4427*25000000000000^3403 ≤ 11091286341523^3403*10000000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5354068187 10000000000 11091286341523 25000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (410972047/2000000000 : ℝ)^4427 ≤ (6382060988927/50000000000000 : ℝ)^3403 := by
    have hnat : (410972047 : ℕ)^4427*50000000000000^3403 ≤ 6382060988927^3403*2000000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      410972047 2000000000 6382060988927 50000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1303722007/2500000000 : ℝ)^4427 ≤ (21435366320139/50000000000000 : ℝ)^3403 := by
    have hnat : (1303722007 : ℕ)^4427*50000000000000^3403 ≤ 21435366320139^3403*2500000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1303722007 2500000000 21435366320139 50000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4427/1024 : ℝ)) 4427 3403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5354068187/10000000000 : ℝ), (-410972047/2000000000 : ℝ), (1303722007/2500000000 : ℝ)] ![(11091286341523/25000000000000 : ℝ), (6382060988927/50000000000000 : ℝ), (21435366320139/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5354068187/10000000000 : ℝ)|^4427 ≤ (11091286341523/25000000000000 : ℝ)^3403
        have hw : |(5354068187/10000000000 : ℝ)|=(5354068187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-410972047/2000000000 : ℝ)|^4427 ≤ (6382060988927/50000000000000 : ℝ)^3403
        have hw : |(-410972047/2000000000 : ℝ)|=(410972047/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1303722007/2500000000 : ℝ)|^4427 ≤ (21435366320139/50000000000000 : ℝ)^3403
        have hw : |(1303722007/2500000000 : ℝ)|=(1303722007/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1465_s6_2 (p : ℝ) (hpa : (4425/1024 : ℝ) ≤ p) (hpb : p ≤ (4427/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5354068239/10000000000 : ℝ)*x 0 + (1303721999/2500000000 : ℝ)*x 1 + (-2054860209/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5354068239/10000000000 : ℝ)^4427 ≤ (8873029185327/20000000000000 : ℝ)^3403 := by
    have hnat : (5354068239 : ℕ)^4427*20000000000000^3403 ≤ 8873029185327^3403*10000000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5354068239 10000000000 8873029185327 20000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1303721999/2500000000 : ℝ)^4427 ≤ (10717683074513/25000000000000 : ℝ)^3403 := by
    have hnat : (1303721999 : ℕ)^4427*25000000000000^3403 ≤ 10717683074513^3403*2500000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1303721999 2500000000 10717683074513 25000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2054860209/10000000000 : ℝ)^4427 ≤ (1595515220969/12500000000000 : ℝ)^3403 := by
    have hnat : (2054860209 : ℕ)^4427*12500000000000^3403 ≤ 1595515220969^3403*10000000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2054860209 10000000000 1595515220969 12500000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4427/1024 : ℝ)) 4427 3403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5354068239/10000000000 : ℝ), (1303721999/2500000000 : ℝ), (-2054860209/10000000000 : ℝ)] ![(8873029185327/20000000000000 : ℝ), (10717683074513/25000000000000 : ℝ), (1595515220969/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5354068239/10000000000 : ℝ)|^4427 ≤ (8873029185327/20000000000000 : ℝ)^3403
        have hw : |(5354068239/10000000000 : ℝ)|=(5354068239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1303721999/2500000000 : ℝ)|^4427 ≤ (10717683074513/25000000000000 : ℝ)^3403
        have hw : |(1303721999/2500000000 : ℝ)|=(1303721999/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2054860209/10000000000 : ℝ)|^4427 ≤ (1595515220969/12500000000000 : ℝ)^3403
        have hw : |(-2054860209/10000000000 : ℝ)|=(2054860209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1465_s6_3 (p : ℝ) (hpa : (4425/1024 : ℝ) ≤ p) (hpb : p ≤ (4427/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1073043347/2500000000 : ℝ)*x 0 + (506531/1250000 : ℝ)*x 1 + (4544569219/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1073043347/2500000000 : ℝ)^4427 ≤ (16638563269203/50000000000000 : ℝ)^3403 := by
    have hnat : (1073043347 : ℕ)^4427*50000000000000^3403 ≤ 16638563269203^3403*2500000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1073043347 2500000000 16638563269203 50000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (506531/1250000 : ℝ)^4427 ≤ (30877878071497/100000000000000 : ℝ)^3403 := by
    have hnat : (506531 : ℕ)^4427*100000000000000^3403 ≤ 30877878071497^3403*1250000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      506531 1250000 30877878071497 100000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4544569219/10000000000 : ℝ)^4427 ≤ (17922497686123/50000000000000 : ℝ)^3403 := by
    have hnat : (4544569219 : ℕ)^4427*50000000000000^3403 ≤ 17922497686123^3403*10000000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4544569219 10000000000 17922497686123 50000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4427/1024 : ℝ)) 4427 3403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1073043347/2500000000 : ℝ), (506531/1250000 : ℝ), (4544569219/10000000000 : ℝ)] ![(16638563269203/50000000000000 : ℝ), (30877878071497/100000000000000 : ℝ), (17922497686123/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1073043347/2500000000 : ℝ)|^4427 ≤ (16638563269203/50000000000000 : ℝ)^3403
        have hw : |(1073043347/2500000000 : ℝ)|=(1073043347/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(506531/1250000 : ℝ)|^4427 ≤ (30877878071497/100000000000000 : ℝ)^3403
        have hw : |(506531/1250000 : ℝ)|=(506531/1250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4544569219/10000000000 : ℝ)|^4427 ≤ (17922497686123/50000000000000 : ℝ)^3403
        have hw : |(4544569219/10000000000 : ℝ)|=(4544569219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1465_s6_4 (p : ℝ) (hpa : (4425/1024 : ℝ) ≤ p) (hpb : p ≤ (4427/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-387956709/2000000000 : ℝ)*x 0 + (260801671/500000000 : ℝ)*x 1 + (2719131209/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (387956709/2000000000 : ℝ)^4427 ≤ (5921073165639/50000000000000 : ℝ)^3403 := by
    have hnat : (387956709 : ℕ)^4427*50000000000000^3403 ≤ 5921073165639^3403*2000000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      387956709 2000000000 5921073165639 50000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (260801671/500000000 : ℝ)^4427 ≤ (10720745631143/25000000000000 : ℝ)^3403 := by
    have hnat : (260801671 : ℕ)^4427*25000000000000^3403 ≤ 10720745631143^3403*500000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      260801671 500000000 10720745631143 25000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2719131209/5000000000 : ℝ)^4427 ≤ (45274871130209/100000000000000 : ℝ)^3403 := by
    have hnat : (2719131209 : ℕ)^4427*100000000000000^3403 ≤ 45274871130209^3403*5000000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2719131209 5000000000 45274871130209 100000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4427/1024 : ℝ)) 4427 3403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-387956709/2000000000 : ℝ), (260801671/500000000 : ℝ), (2719131209/5000000000 : ℝ)] ![(5921073165639/50000000000000 : ℝ), (10720745631143/25000000000000 : ℝ), (45274871130209/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-387956709/2000000000 : ℝ)|^4427 ≤ (5921073165639/50000000000000 : ℝ)^3403
        have hw : |(-387956709/2000000000 : ℝ)|=(387956709/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(260801671/500000000 : ℝ)|^4427 ≤ (10720745631143/25000000000000 : ℝ)^3403
        have hw : |(260801671/500000000 : ℝ)|=(260801671/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2719131209/5000000000 : ℝ)|^4427 ≤ (45274871130209/100000000000000 : ℝ)^3403
        have hw : |(2719131209/5000000000 : ℝ)|=(2719131209/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1465_s6_5 (p : ℝ) (hpa : (4425/1024 : ℝ) ≤ p) (hpb : p ≤ (4427/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2647792369/5000000000 : ℝ)*x 0 + (-36629717/200000000 : ℝ)*x 1 + (5438262417/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2647792369/5000000000 : ℝ)^4427 ≤ (21867875824699/50000000000000 : ℝ)^3403 := by
    have hnat : (2647792369 : ℕ)^4427*50000000000000^3403 ≤ 21867875824699^3403*5000000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647792369 5000000000 21867875824699 50000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (36629717/200000000 : ℝ)^4427 ≤ (10989377211209/100000000000000 : ℝ)^3403 := by
    have hnat : (36629717 : ℕ)^4427*100000000000000^3403 ≤ 10989377211209^3403*200000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      36629717 200000000 10989377211209 100000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5438262417/10000000000 : ℝ)^4427 ≤ (45274871119379/100000000000000 : ℝ)^3403 := by
    have hnat : (5438262417 : ℕ)^4427*100000000000000^3403 ≤ 45274871119379^3403*10000000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5438262417 10000000000 45274871119379 100000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4427/1024 : ℝ)) 4427 3403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2647792369/5000000000 : ℝ), (-36629717/200000000 : ℝ), (5438262417/10000000000 : ℝ)] ![(21867875824699/50000000000000 : ℝ), (10989377211209/100000000000000 : ℝ), (45274871119379/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2647792369/5000000000 : ℝ)|^4427 ≤ (21867875824699/50000000000000 : ℝ)^3403
        have hw : |(2647792369/5000000000 : ℝ)|=(2647792369/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-36629717/200000000 : ℝ)|^4427 ≤ (10989377211209/100000000000000 : ℝ)^3403
        have hw : |(-36629717/200000000 : ℝ)|=(36629717/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5438262417/10000000000 : ℝ)|^4427 ≤ (45274871119379/100000000000000 : ℝ)^3403
        have hw : |(5438262417/10000000000 : ℝ)|=(5438262417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1465_s6_6 (p : ℝ) (hpa : (4425/1024 : ℝ) ≤ p) (hpb : p ≤ (4427/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1059116949/2000000000 : ℝ)*x 0 + (2719131209/5000000000 : ℝ)*x 1 + (-22893573/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1059116949/2000000000 : ℝ)^4427 ≤ (43735751724607/100000000000000 : ℝ)^3403 := by
    have hnat : (1059116949 : ℕ)^4427*100000000000000^3403 ≤ 43735751724607^3403*2000000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1059116949 2000000000 43735751724607 100000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2719131209/5000000000 : ℝ)^4427 ≤ (45274871130209/100000000000000 : ℝ)^3403 := by
    have hnat : (2719131209 : ℕ)^4427*100000000000000^3403 ≤ 45274871130209^3403*5000000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2719131209 5000000000 45274871130209 100000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (22893573/125000000 : ℝ)^4427 ≤ (10989377133151/100000000000000 : ℝ)^3403 := by
    have hnat : (22893573 : ℕ)^4427*100000000000000^3403 ≤ 10989377133151^3403*125000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      22893573 125000000 10989377133151 100000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4427/1024 : ℝ)) 4427 3403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1059116949/2000000000 : ℝ), (2719131209/5000000000 : ℝ), (-22893573/125000000 : ℝ)] ![(43735751724607/100000000000000 : ℝ), (45274871130209/100000000000000 : ℝ), (10989377133151/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1059116949/2000000000 : ℝ)|^4427 ≤ (43735751724607/100000000000000 : ℝ)^3403
        have hw : |(1059116949/2000000000 : ℝ)|=(1059116949/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2719131209/5000000000 : ℝ)|^4427 ≤ (45274871130209/100000000000000 : ℝ)^3403
        have hw : |(2719131209/5000000000 : ℝ)|=(2719131209/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-22893573/125000000 : ℝ)|^4427 ≤ (10989377133151/100000000000000 : ℝ)^3403
        have hw : |(-22893573/125000000 : ℝ)|=(22893573/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1465_s6_7 (p : ℝ) (hpa : (4425/1024 : ℝ) ≤ p) (hpb : p ≤ (4427/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4292241463/10000000000 : ℝ)*x 0 + (56775723/125000000 : ℝ)*x 1 + (126711807/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4292241463/10000000000 : ℝ)^4427 ≤ (33277813140019/100000000000000 : ℝ)^3403 := by
    have hnat : (4292241463 : ℕ)^4427*100000000000000^3403 ≤ 33277813140019^3403*10000000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4292241463 10000000000 33277813140019 100000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (56775723/125000000 : ℝ)^4427 ≤ (35819228629443/100000000000000 : ℝ)^3403 := by
    have hnat : (56775723 : ℕ)^4427*100000000000000^3403 ≤ 35819228629443^3403*125000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      56775723 125000000 35819228629443 100000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (126711807/312500000 : ℝ)^4427 ≤ (15451479109831/50000000000000 : ℝ)^3403 := by
    have hnat : (126711807 : ℕ)^4427*50000000000000^3403 ≤ 15451479109831^3403*312500000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      126711807 312500000 15451479109831 50000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4427/1024 : ℝ)) 4427 3403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4292241463/10000000000 : ℝ), (56775723/125000000 : ℝ), (126711807/312500000 : ℝ)] ![(33277813140019/100000000000000 : ℝ), (35819228629443/100000000000000 : ℝ), (15451479109831/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4292241463/10000000000 : ℝ)|^4427 ≤ (33277813140019/100000000000000 : ℝ)^3403
        have hw : |(4292241463/10000000000 : ℝ)|=(4292241463/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(56775723/125000000 : ℝ)|^4427 ≤ (35819228629443/100000000000000 : ℝ)^3403
        have hw : |(56775723/125000000 : ℝ)|=(56775723/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(126711807/312500000 : ℝ)|^4427 ≤ (15451479109831/50000000000000 : ℝ)^3403
        have hw : |(126711807/312500000 : ℝ)|=(126711807/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1465_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4425/1024 : ℝ) ≤ p) (hpb : p ≤ (4427/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79817329/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15473/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10719/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10721/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15471/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15473/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10719/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15473/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10719/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15473/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10719/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15473/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10719/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15473/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10719/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15473/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10719/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10719/100000 : ℝ) ^ (4425/1024 : ℝ) ≤ (6441933816436103/100000000000000000000 : ℝ) := by
    have hpowers : (10719/100000 : ℝ)^4425 ≤ (6441933816436103/100000000000000000000 : ℝ)^1024 := by
      have hnat : (10719 : ℕ)^4425*100000000000000000000^1024 ≤ 6441933816436103^1024*100000^4425 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10719 100000 6441933816436103 100000000000000000000 4425 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10719/100000 : ℝ)) (X := (6441933816436103/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4425 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15473/100000 : ℝ) ^ (4425/1024 : ℝ) ≤ (31471486840832477/100000000000000000000 : ℝ) := by
    have hpowers : (15473/100000 : ℝ)^4425 ≤ (31471486840832477/100000000000000000000 : ℝ)^1024 := by
      have hnat : (15473 : ℕ)^4425*100000000000000000000^1024 ≤ 31471486840832477^1024*100000^4425 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15473 100000 31471486840832477 100000000000000000000 4425 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15473/100000 : ℝ)) (X := (31471486840832477/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4425 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50006441933816436103/50000000000000000000 : ℝ) ≤ (10000298133950083/10000000000000000 : ℝ) ^ (4425/1024 : ℝ) := by
    have hpowers : (50006441933816436103/50000000000000000000 : ℝ)^1024 ≤ (10000298133950083/10000000000000000 : ℝ)^4425 := by
      have hnat : (50006441933816436103 : ℕ)^1024*10000000000000000^4425 ≤ 10000298133950083^4425*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50006441933816436103 50000000000000000000 10000298133950083 10000000000000000 1024 4425 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000298133950083/10000000000000000 : ℝ)) (X := (50006441933816436103/50000000000000000000 : ℝ)) (by norm_num) 4425 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (5001895671032863429/5000000000000000000 : ℝ) ≤ (500043861793783/500000000000000 : ℝ) ^ (4425/1024 : ℝ) := by
    have hpowers : (5001895671032863429/5000000000000000000 : ℝ)^1024 ≤ (500043861793783/500000000000000 : ℝ)^4425 := by
      have hnat : (5001895671032863429 : ℕ)^1024*500000000000000^4425 ≤ 500043861793783^4425*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5001895671032863429 5000000000000000000 500043861793783 500000000000000 1024 4425 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500043861793783/500000000000000 : ℝ)) (X := (5001895671032863429/5000000000000000000 : ℝ)) (by norm_num) 4425 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50031471486840832477/50000000000000000000 : ℝ) ≤ (10001456337801237/10000000000000000 : ℝ) ^ (4425/1024 : ℝ) := by
    have hpowers : (50031471486840832477/50000000000000000000 : ℝ)^1024 ≤ (10001456337801237/10000000000000000 : ℝ)^4425 := by
      have hnat : (50031471486840832477 : ℕ)^1024*10000000000000000^4425 ≤ 10001456337801237^4425*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50031471486840832477 50000000000000000000 10001456337801237 10000000000000000 1024 4425 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001456337801237/10000000000000000 : ℝ)) (X := (50031471486840832477/50000000000000000000 : ℝ)) (by norm_num) 4425 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6441933816436103/100000000000000000000 : ℝ) ≤ ((5941125317714771857/5942500000000000000 : ℝ)+2*(579101925577/475400000000000 : ℝ)*(10719/100000 : ℝ))^(4425/1024 : ℝ) := by
    rw [show (5941125317714771857/5942500000000000000 : ℝ)+2*(579101925577/475400000000000 : ℝ)*(10719/100000 : ℝ)=(10000298133950083/10000000000000000 : ℝ) by norm_num, show 1+2*(6441933816436103/100000000000000000000 : ℝ)=(50006441933816436103/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(31471486840832477/100000000000000000000 : ℝ)+(6441933816436103/100000000000000000000 : ℝ) ≤ ((5941125317714771857/5942500000000000000 : ℝ)+(579101925577/475400000000000 : ℝ)*((15473/100000 : ℝ)+(10719/100000 : ℝ)))^(4425/1024 : ℝ) := by
    rw [show (5941125317714771857/5942500000000000000 : ℝ)+(579101925577/475400000000000 : ℝ)*((15473/100000 : ℝ)+(10719/100000 : ℝ))=(500043861793783/500000000000000 : ℝ) by norm_num, show 1+(31471486840832477/100000000000000000000 : ℝ)+(6441933816436103/100000000000000000000 : ℝ)=(5001895671032863429/5000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(31471486840832477/100000000000000000000 : ℝ) ≤ ((5941125317714771857/5942500000000000000 : ℝ)+2*(579101925577/475400000000000 : ℝ)*(15473/100000 : ℝ))^(4425/1024 : ℝ) := by
    rw [show (5941125317714771857/5942500000000000000 : ℝ)+2*(579101925577/475400000000000 : ℝ)*(15473/100000 : ℝ)=(10001456337801237/10000000000000000 : ℝ) by norm_num, show 1+2*(31471486840832477/100000000000000000000 : ℝ)=(50031471486840832477/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5941125317714771857/5942500000000000000 : ℝ)*(X 1 0+X 2 0)+(579101925577/475400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4425/1024 : ℝ)) (lo := (10719/100000 : ℝ)) (hi := (15473/100000 : ℝ)) (c := (5941125317714771857/5942500000000000000 : ℝ)) (alpha := (579101925577/475400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5941125317714771857/5942500000000000000 : ℝ)*(X 0 1+X 2 1)+(579101925577/475400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4425/1024 : ℝ)) (lo := (10719/100000 : ℝ)) (hi := (15473/100000 : ℝ)) (c := (5941125317714771857/5942500000000000000 : ℝ)) (alpha := (579101925577/475400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5941125317714771857/5942500000000000000 : ℝ)*(X 0 2+X 1 2)+(579101925577/475400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4425/1024 : ℝ)) (lo := (10719/100000 : ℝ)) (hi := (15473/100000 : ℝ)) (c := (5941125317714771857/5942500000000000000 : ℝ)) (alpha := (579101925577/475400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-77590101/400000000 : ℝ)*X 0 0+(42495439/78125000 : ℝ)*X 0 1+(1303722007/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1465_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5354068187/10000000000 : ℝ)*X 1 0+(-410972047/2000000000 : ℝ)*X 1 1+(1303722007/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1465_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5354068239/10000000000 : ℝ)*X 2 0+(1303721999/2500000000 : ℝ)*X 2 1+(-2054860209/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1465_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1073043347/2500000000 : ℝ)*X 0 0+(506531/1250000 : ℝ)*X 0 1+(4544569219/10000000000 : ℝ)*X 0 2+(1073043347/2500000000 : ℝ)*X 1 0+(506531/1250000 : ℝ)*X 1 1+(4544569219/10000000000 : ℝ)*X 1 2+(1073043347/2500000000 : ℝ)*X 2 0+(506531/1250000 : ℝ)*X 2 1+(4544569219/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1465_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-387956709/2000000000 : ℝ)*X 0 0+(260801671/500000000 : ℝ)*X 0 1+(2719131209/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1465_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2647792369/5000000000 : ℝ)*X 1 0+(-36629717/200000000 : ℝ)*X 1 1+(5438262417/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1465_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1059116949/2000000000 : ℝ)*X 2 0+(2719131209/5000000000 : ℝ)*X 2 1+(-22893573/125000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1465_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4292241463/10000000000 : ℝ)*X 0 0+(56775723/125000000 : ℝ)*X 0 1+(126711807/312500000 : ℝ)*X 0 2+(4292241463/10000000000 : ℝ)*X 1 0+(56775723/125000000 : ℝ)*X 1 1+(126711807/312500000 : ℝ)*X 1 2+(4292241463/10000000000 : ℝ)*X 2 0+(56775723/125000000 : ℝ)*X 2 1+(126711807/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1465_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (14939446557456375099723/4754000000000000000000000000 : ℝ) := by norm_num
    linear_combination (77240937/12500000000000 : ℝ)*(base19) + (40261159/6250000000000 : ℝ)*(base23) + (2276197/25000000000000 : ℝ)*(lower2) + (63690717/100000000000000 : ℝ)*(upper3) + (5182897/6250000000000 : ℝ)*(upper5) + (648500670343393/20000000000000 : ℝ)*(major0) + (648500670343393/20000000000000 : ℝ)*(major1) + (648500670343393/20000000000000 : ℝ)*(major2) + (556724199411191/12500000000000 : ℝ)*(sp0) + (556725420408321/12500000000000 : ℝ)*(sp1) + (27836270856347/625000000000 : ℝ)*(sp2) + (406239681101447/20000000000000 : ℝ)*(sp3) + (10385904537/100000000000000 : ℝ)*(sp4) + (1052995653/25000000000000 : ℝ)*(sp7) + (2031202617489847/100000000000000 : ℝ)*(f.failure) + (890760796238813/20000000000000 : ℝ)*(f.sum) + (22532162118827/4754000000000000000000000000 : ℝ)*base65 + (880131670597796699/118850000000000000000000000000000 : ℝ)*base68 + (309608291179746699/118850000000000000000000000000000 : ℝ)*base70 + (97011639498396699/118850000000000000000000000000000 : ℝ)*base72 + (34477962425639/4754000000000000000000000000 : ℝ)*base74 + (501889209992353301/118850000000000000000000000000000 : ℝ)*base75 + (788112199445203301/118850000000000000000000000000000 : ℝ)*base77 + (1228168208026803301/118850000000000000000000000000000 : ℝ)*base79 + (11212444892281/4754000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (22158663/5000000000000000000000 : ℝ)*base89 + (22158663/5000000000000000000000 : ℝ)*base91 + (22158663/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (735243988210137495512518413/148562500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (205141469/25000000000000 : ℝ)*(base19) + (901541423/100000000000000 : ℝ)*(base23) + (33856271/12500000000000 : ℝ)*(lower1) + (51510231/50000000000000 : ℝ)*(upper3) + (6501293/20000000000000 : ℝ)*(lower4) + (10070703/10000000000000 : ℝ)*(upper5) + (1638013163757703/50000000000000 : ℝ)*(major0) + (1638013163757703/50000000000000 : ℝ)*(major1) + (1638013163757703/50000000000000 : ℝ)*(major2) + (308844823/25000000000000 : ℝ)*(sp2) + (1124962515498361/25000000000000 : ℝ)*(sp4) + (281240577589223/6250000000000 : ℝ)*(sp5) + (449984792507273/10000000000000 : ℝ)*(sp6) + (41044048561377/2000000000000 : ℝ)*(sp7) + (41044048561377/2000000000000 : ℝ)*(f.failure) + (1124962515498361/25000000000000 : ℝ)*(f.sum) + (52098843215181/11885000000000000000000000000 : ℝ)*base65 + (1502164349028248029/297125000000000000000000000000000 : ℝ)*base68 + (2647873373968751971/297125000000000000000000000000000 : ℝ)*base69 + (6393456456252001971/297125000000000000000000000000000 : ℝ)*base71 + (37947104757631/11885000000000000000000000000 : ℝ)*base73 + (10964767147972248029/297125000000000000000000000000000 : ℝ)*base76 + (1327560538767748029/297125000000000000000000000000000 : ℝ)*base78 + (2128664739838748029/297125000000000000000000000000000 : ℝ)*base80 + (33237364830411/11885000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (1297967/100000000000000000000 : ℝ)*base90 + (1297967/100000000000000000000 : ℝ)*base92 + (1297967/100000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1465_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4425/1024 : ℝ) ≤ p) (hpb : p ≤ (4427/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79817329/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15473/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10719/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10721/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15471/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1465_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1465_box_0 (p : ℝ) (hpa : (4425/1024 : ℝ) ≤ p) (hpb : p ≤ (4427/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-107332351/625000000 : ℝ)*x 0 + (1081586399/2000000000 : ℝ)*x 1 + (5407932063/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (107332351/625000000 : ℝ)^4427 ≤ (10106686422323/100000000000000 : ℝ)^3403 := by
    have hnat : (107332351 : ℕ)^4427*100000000000000^3403 ≤ 10106686422323^3403*625000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107332351 625000000 10106686422323 100000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1081586399/2000000000 : ℝ)^4427 ≤ (2809166025979/6250000000000 : ℝ)^3403 := by
    have hnat : (1081586399 : ℕ)^4427*6250000000000^3403 ≤ 2809166025979^3403*2000000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081586399 2000000000 2809166025979 6250000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5407932063/10000000000 : ℝ)^4427 ≤ (44946657150893/100000000000000 : ℝ)^3403 := by
    have hnat : (5407932063 : ℕ)^4427*100000000000000^3403 ≤ 44946657150893^3403*10000000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5407932063 10000000000 44946657150893 100000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4427/1024 : ℝ)) 4427 3403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-107332351/625000000 : ℝ), (1081586399/2000000000 : ℝ), (5407932063/10000000000 : ℝ)] ![(10106686422323/100000000000000 : ℝ), (2809166025979/6250000000000 : ℝ), (44946657150893/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-107332351/625000000 : ℝ)|^4427 ≤ (10106686422323/100000000000000 : ℝ)^3403
        have hw : |(-107332351/625000000 : ℝ)|=(107332351/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1081586399/2000000000 : ℝ)|^4427 ≤ (2809166025979/6250000000000 : ℝ)^3403
        have hw : |(1081586399/2000000000 : ℝ)|=(1081586399/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5407932063/10000000000 : ℝ)|^4427 ≤ (44946657150893/100000000000000 : ℝ)^3403
        have hw : |(5407932063/10000000000 : ℝ)|=(5407932063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1465_box_1 (p : ℝ) (hpa : (4425/1024 : ℝ) ≤ p) (hpb : p ≤ (4427/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (329367611/625000000 : ℝ)*x 0 + (-190840473/1000000000 : ℝ)*x 1 + (5407931789/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (329367611/625000000 : ℝ)^4427 ≤ (21729899109657/50000000000000 : ℝ)^3403 := by
    have hnat : (329367611 : ℕ)^4427*50000000000000^3403 ≤ 21729899109657^3403*625000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      329367611 625000000 21729899109657 50000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (190840473/1000000000 : ℝ)^4427 ≤ (11593547574631/100000000000000 : ℝ)^3403 := by
    have hnat : (190840473 : ℕ)^4427*100000000000000^3403 ≤ 11593547574631^3403*1000000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      190840473 1000000000 11593547574631 100000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5407931789/10000000000 : ℝ)^4427 ≤ (44946654188353/100000000000000 : ℝ)^3403 := by
    have hnat : (5407931789 : ℕ)^4427*100000000000000^3403 ≤ 44946654188353^3403*10000000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5407931789 10000000000 44946654188353 100000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4427/1024 : ℝ)) 4427 3403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(329367611/625000000 : ℝ), (-190840473/1000000000 : ℝ), (5407931789/10000000000 : ℝ)] ![(21729899109657/50000000000000 : ℝ), (11593547574631/100000000000000 : ℝ), (44946654188353/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(329367611/625000000 : ℝ)|^4427 ≤ (21729899109657/50000000000000 : ℝ)^3403
        have hw : |(329367611/625000000 : ℝ)|=(329367611/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-190840473/1000000000 : ℝ)|^4427 ≤ (11593547574631/100000000000000 : ℝ)^3403
        have hw : |(-190840473/1000000000 : ℝ)|=(190840473/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5407931789/10000000000 : ℝ)|^4427 ≤ (44946654188353/100000000000000 : ℝ)^3403
        have hw : |(5407931789/10000000000 : ℝ)|=(5407931789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1465_box_2 (p : ℝ) (hpa : (4425/1024 : ℝ) ≤ p) (hpb : p ≤ (4427/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2634941659/5000000000 : ℝ)*x 0 + (1351982799/2500000000 : ℝ)*x 1 + (-1908403449/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2634941659/5000000000 : ℝ)^4427 ≤ (43459814762487/100000000000000 : ℝ)^3403 := by
    have hnat : (2634941659 : ℕ)^4427*100000000000000^3403 ≤ 43459814762487^3403*5000000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2634941659 5000000000 43459814762487 100000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1351982799/2500000000 : ℝ)^4427 ≤ (44946647776723/100000000000000 : ℝ)^3403 := by
    have hnat : (1351982799 : ℕ)^4427*100000000000000^3403 ≤ 44946647776723^3403*2500000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1351982799 2500000000 44946647776723 100000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1908403449/10000000000 : ℝ)^4427 ≤ (2318707490171/20000000000000 : ℝ)^3403 := by
    have hnat : (1908403449 : ℕ)^4427*20000000000000^3403 ≤ 2318707490171^3403*10000000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1908403449 10000000000 2318707490171 20000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4427/1024 : ℝ)) 4427 3403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2634941659/5000000000 : ℝ), (1351982799/2500000000 : ℝ), (-1908403449/10000000000 : ℝ)] ![(43459814762487/100000000000000 : ℝ), (44946647776723/100000000000000 : ℝ), (2318707490171/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2634941659/5000000000 : ℝ)|^4427 ≤ (43459814762487/100000000000000 : ℝ)^3403
        have hw : |(2634941659/5000000000 : ℝ)|=(2634941659/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1351982799/2500000000 : ℝ)|^4427 ≤ (44946647776723/100000000000000 : ℝ)^3403
        have hw : |(1351982799/2500000000 : ℝ)|=(1351982799/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1908403449/10000000000 : ℝ)|^4427 ≤ (2318707490171/20000000000000 : ℝ)^3403
        have hw : |(-1908403449/10000000000 : ℝ)|=(1908403449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1465_box_3 (p : ℝ) (hpa : (4425/1024 : ℝ) ≤ p) (hpb : p ≤ (4427/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4497561983/10000000000 : ℝ)*x 0 + (2098392543/5000000000 : ℝ)*x 1 + (4196787699/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4497561983/10000000000 : ℝ)^4427 ≤ (7072682716259/20000000000000 : ℝ)^3403 := by
    have hnat : (4497561983 : ℕ)^4427*20000000000000^3403 ≤ 7072682716259^3403*10000000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4497561983 10000000000 7072682716259 20000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2098392543/5000000000 : ℝ)^4427 ≤ (3231828011003/10000000000000 : ℝ)^3403 := by
    have hnat : (2098392543 : ℕ)^4427*10000000000000^3403 ≤ 3231828011003^3403*5000000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2098392543 5000000000 3231828011003 10000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4196787699/10000000000 : ℝ)^4427 ≤ (646366125739/2000000000000 : ℝ)^3403 := by
    have hnat : (4196787699 : ℕ)^4427*2000000000000^3403 ≤ 646366125739^3403*10000000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4196787699 10000000000 646366125739 2000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4427/1024 : ℝ)) 4427 3403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4497561983/10000000000 : ℝ), (2098392543/5000000000 : ℝ), (4196787699/10000000000 : ℝ)] ![(7072682716259/20000000000000 : ℝ), (3231828011003/10000000000000 : ℝ), (646366125739/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4497561983/10000000000 : ℝ)|^4427 ≤ (7072682716259/20000000000000 : ℝ)^3403
        have hw : |(4497561983/10000000000 : ℝ)|=(4497561983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2098392543/5000000000 : ℝ)|^4427 ≤ (3231828011003/10000000000000 : ℝ)^3403
        have hw : |(2098392543/5000000000 : ℝ)|=(2098392543/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4196787699/10000000000 : ℝ)|^4427 ≤ (646366125739/2000000000000 : ℝ)^3403
        have hw : |(4196787699/10000000000 : ℝ)|=(4196787699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1465_box_4 (p : ℝ) (hpa : (4425/1024 : ℝ) ≤ p) (hpb : p ≤ (4427/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-541916823/2500000000 : ℝ)*x 0 + (2620884281/5000000000 : ℝ)*x 1 + (163805283/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (541916823/2500000000 : ℝ)^4427 ≤ (855195770867/6250000000000 : ℝ)^3403 := by
    have hnat : (541916823 : ℕ)^4427*6250000000000^3403 ≤ 855195770867^3403*2500000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      541916823 2500000000 855195770867 6250000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2620884281/5000000000 : ℝ)^4427 ≤ (43158431180827/100000000000000 : ℝ)^3403 := by
    have hnat : (2620884281 : ℕ)^4427*100000000000000^3403 ≤ 43158431180827^3403*5000000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2620884281 5000000000 43158431180827 100000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (163805283/312500000 : ℝ)^4427 ≤ (43158436472127/100000000000000 : ℝ)^3403 := by
    have hnat : (163805283 : ℕ)^4427*100000000000000^3403 ≤ 43158436472127^3403*312500000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      163805283 312500000 43158436472127 100000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4427/1024 : ℝ)) 4427 3403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-541916823/2500000000 : ℝ), (2620884281/5000000000 : ℝ), (163805283/312500000 : ℝ)] ![(855195770867/6250000000000 : ℝ), (43158431180827/100000000000000 : ℝ), (43158436472127/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-541916823/2500000000 : ℝ)|^4427 ≤ (855195770867/6250000000000 : ℝ)^3403
        have hw : |(-541916823/2500000000 : ℝ)|=(541916823/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2620884281/5000000000 : ℝ)|^4427 ≤ (43158431180827/100000000000000 : ℝ)^3403
        have hw : |(2620884281/5000000000 : ℝ)|=(2620884281/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(163805283/312500000 : ℝ)|^4427 ≤ (43158436472127/100000000000000 : ℝ)^3403
        have hw : |(163805283/312500000 : ℝ)|=(163805283/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1465_box_5 (p : ℝ) (hpa : (4425/1024 : ℝ) ≤ p) (hpb : p ≤ (4427/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2692998831/5000000000 : ℝ)*x 0 + (-1976168441/10000000000 : ℝ)*x 1 + (5241768753/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2692998831/5000000000 : ℝ)^4427 ≤ (44709643060833/100000000000000 : ℝ)^3403 := by
    have hnat : (2692998831 : ℕ)^4427*100000000000000^3403 ≤ 44709643060833^3403*5000000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2692998831 5000000000 44709643060833 100000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1976168441/10000000000 : ℝ)^4427 ≤ (12131923703081/100000000000000 : ℝ)^3403 := by
    have hnat : (1976168441 : ℕ)^4427*100000000000000^3403 ≤ 12131923703081^3403*10000000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1976168441 10000000000 12131923703081 100000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5241768753/10000000000 : ℝ)^4427 ≤ (43158433226653/100000000000000 : ℝ)^3403 := by
    have hnat : (5241768753 : ℕ)^4427*100000000000000^3403 ≤ 43158433226653^3403*10000000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5241768753 10000000000 43158433226653 100000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4427/1024 : ℝ)) 4427 3403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2692998831/5000000000 : ℝ), (-1976168441/10000000000 : ℝ), (5241768753/10000000000 : ℝ)] ![(44709643060833/100000000000000 : ℝ), (12131923703081/100000000000000 : ℝ), (43158433226653/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2692998831/5000000000 : ℝ)|^4427 ≤ (44709643060833/100000000000000 : ℝ)^3403
        have hw : |(2692998831/5000000000 : ℝ)|=(2692998831/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1976168441/10000000000 : ℝ)|^4427 ≤ (12131923703081/100000000000000 : ℝ)^3403
        have hw : |(-1976168441/10000000000 : ℝ)|=(1976168441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5241768753/10000000000 : ℝ)|^4427 ≤ (43158433226653/100000000000000 : ℝ)^3403
        have hw : |(5241768753/10000000000 : ℝ)|=(5241768753/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1465_box_6 (p : ℝ) (hpa : (4425/1024 : ℝ) ≤ p) (hpb : p ≤ (4427/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5385997821/10000000000 : ℝ)*x 0 + (5241768819/10000000000 : ℝ)*x 1 + (-988084069/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5385997821/10000000000 : ℝ)^4427 ≤ (4470964477787/10000000000000 : ℝ)^3403 := by
    have hnat : (5385997821 : ℕ)^4427*10000000000000^3403 ≤ 4470964477787^3403*10000000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5385997821 10000000000 4470964477787 10000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5241768819/10000000000 : ℝ)^4427 ≤ (10789608483397/25000000000000 : ℝ)^3403 := by
    have hnat : (5241768819 : ℕ)^4427*25000000000000^3403 ≤ 10789608483397^3403*10000000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5241768819 10000000000 10789608483397 25000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (988084069/5000000000 : ℝ)^4427 ≤ (12131921283189/100000000000000 : ℝ)^3403 := by
    have hnat : (988084069 : ℕ)^4427*100000000000000^3403 ≤ 12131921283189^3403*5000000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      988084069 5000000000 12131921283189 100000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4427/1024 : ℝ)) 4427 3403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5385997821/10000000000 : ℝ), (5241768819/10000000000 : ℝ), (-988084069/5000000000 : ℝ)] ![(4470964477787/10000000000000 : ℝ), (10789608483397/25000000000000 : ℝ), (12131921283189/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5385997821/10000000000 : ℝ)|^4427 ≤ (4470964477787/10000000000000 : ℝ)^3403
        have hw : |(5385997821/10000000000 : ℝ)|=(5385997821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5241768819/10000000000 : ℝ)|^4427 ≤ (10789608483397/25000000000000 : ℝ)^3403
        have hw : |(5241768819/10000000000 : ℝ)|=(5241768819/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-988084069/5000000000 : ℝ)|^4427 ≤ (12131921283189/100000000000000 : ℝ)^3403
        have hw : |(-988084069/5000000000 : ℝ)|=(988084069/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1465_box_7 (p : ℝ) (hpa : (4425/1024 : ℝ) ≤ p) (hpb : p ≤ (4427/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (510575717/1250000000 : ℝ)*x 0 + (4403123397/10000000000 : ℝ)*x 1 + (550390487/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (510575717/1250000000 : ℝ)^4427 ≤ (31199020447633/100000000000000 : ℝ)^3403 := by
    have hnat : (510575717 : ℕ)^4427*100000000000000^3403 ≤ 31199020447633^3403*1250000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      510575717 1250000000 31199020447633 100000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4403123397/10000000000 : ℝ)^4427 ≤ (34400487231527/100000000000000 : ℝ)^3403 := by
    have hnat : (4403123397 : ℕ)^4427*100000000000000^3403 ≤ 34400487231527^3403*10000000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4403123397 10000000000 34400487231527 100000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (550390487/1250000000 : ℝ)^4427 ≤ (34400492303207/100000000000000 : ℝ)^3403 := by
    have hnat : (550390487 : ℕ)^4427*100000000000000^3403 ≤ 34400492303207^3403*1250000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      550390487 1250000000 34400492303207 100000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4427/1024 : ℝ)) 4427 3403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(510575717/1250000000 : ℝ), (4403123397/10000000000 : ℝ), (550390487/1250000000 : ℝ)] ![(31199020447633/100000000000000 : ℝ), (34400487231527/100000000000000 : ℝ), (34400492303207/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(510575717/1250000000 : ℝ)|^4427 ≤ (31199020447633/100000000000000 : ℝ)^3403
        have hw : |(510575717/1250000000 : ℝ)|=(510575717/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4403123397/10000000000 : ℝ)|^4427 ≤ (34400487231527/100000000000000 : ℝ)^3403
        have hw : |(4403123397/10000000000 : ℝ)|=(4403123397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(550390487/1250000000 : ℝ)|^4427 ≤ (34400492303207/100000000000000 : ℝ)^3403
        have hw : |(550390487/1250000000 : ℝ)|=(550390487/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1465_box_8 (p : ℝ) (hpa : (4425/1024 : ℝ) ≤ p) (hpb : p ≤ (4427/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-32387173/156250000 : ℝ)*x 0 + (205036099/400000000 : ℝ)*x 1 + (1357129559/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (32387173/156250000 : ℝ)^4427 ≤ (12909110732879/100000000000000 : ℝ)^3403 := by
    have hnat : (32387173 : ℕ)^4427*100000000000000^3403 ≤ 12909110732879^3403*156250000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      32387173 156250000 12909110732879 100000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (205036099/400000000 : ℝ)^4427 ≤ (8384304616063/20000000000000 : ℝ)^3403 := by
    have hnat : (205036099 : ℕ)^4427*20000000000000^3403 ≤ 8384304616063^3403*400000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      205036099 400000000 8384304616063 20000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1357129559/2500000000 : ℝ)^4427 ≤ (11292341542429/25000000000000 : ℝ)^3403 := by
    have hnat : (1357129559 : ℕ)^4427*25000000000000^3403 ≤ 11292341542429^3403*2500000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1357129559 2500000000 11292341542429 25000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4427/1024 : ℝ)) 4427 3403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-32387173/156250000 : ℝ), (205036099/400000000 : ℝ), (1357129559/2500000000 : ℝ)] ![(12909110732879/100000000000000 : ℝ), (8384304616063/20000000000000 : ℝ), (11292341542429/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-32387173/156250000 : ℝ)|^4427 ≤ (12909110732879/100000000000000 : ℝ)^3403
        have hw : |(-32387173/156250000 : ℝ)|=(32387173/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(205036099/400000000 : ℝ)|^4427 ≤ (8384304616063/20000000000000 : ℝ)^3403
        have hw : |(205036099/400000000 : ℝ)|=(205036099/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1357129559/2500000000 : ℝ)|^4427 ≤ (11292341542429/25000000000000 : ℝ)^3403
        have hw : |(1357129559/2500000000 : ℝ)|=(1357129559/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1465_box_9 (p : ℝ) (hpa : (4425/1024 : ℝ) ≤ p) (hpb : p ≤ (4427/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1313872183/2500000000 : ℝ)*x 0 + (-474937333/2500000000 : ℝ)*x 1 + (2714258923/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1313872183/2500000000 : ℝ)^4427 ≤ (43305447574773/100000000000000 : ℝ)^3403 := by
    have hnat : (1313872183 : ℕ)^4427*100000000000000^3403 ≤ 43305447574773^3403*2500000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1313872183 2500000000 43305447574773 100000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (474937333/2500000000 : ℝ)^4427 ≤ (11525190461697/100000000000000 : ℝ)^3403 := by
    have hnat : (474937333 : ℕ)^4427*100000000000000^3403 ≤ 11525190461697^3403*2500000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      474937333 2500000000 11525190461697 100000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2714258923/5000000000 : ℝ)^4427 ≤ (22584680974069/50000000000000 : ℝ)^3403 := by
    have hnat : (2714258923 : ℕ)^4427*50000000000000^3403 ≤ 22584680974069^3403*5000000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2714258923 5000000000 22584680974069 50000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4427/1024 : ℝ)) 4427 3403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1313872183/2500000000 : ℝ), (-474937333/2500000000 : ℝ), (2714258923/5000000000 : ℝ)] ![(43305447574773/100000000000000 : ℝ), (11525190461697/100000000000000 : ℝ), (22584680974069/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1313872183/2500000000 : ℝ)|^4427 ≤ (43305447574773/100000000000000 : ℝ)^3403
        have hw : |(1313872183/2500000000 : ℝ)|=(1313872183/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-474937333/2500000000 : ℝ)|^4427 ≤ (11525190461697/100000000000000 : ℝ)^3403
        have hw : |(-474937333/2500000000 : ℝ)|=(474937333/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2714258923/5000000000 : ℝ)|^4427 ≤ (22584680974069/50000000000000 : ℝ)^3403
        have hw : |(2714258923/5000000000 : ℝ)|=(2714258923/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1465_box_10 (p : ℝ) (hpa : (4425/1024 : ℝ) ≤ p) (hpb : p ≤ (4427/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (656936047/1250000000 : ℝ)*x 0 + (5428517887/10000000000 : ℝ)*x 1 + (-1899749759/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (656936047/1250000000 : ℝ)^4427 ≤ (43305443758609/100000000000000 : ℝ)^3403 := by
    have hnat : (656936047 : ℕ)^4427*100000000000000^3403 ≤ 43305443758609^3403*1250000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      656936047 1250000000 43305443758609 100000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5428517887/10000000000 : ℝ)^4427 ≤ (9033872478389/20000000000000 : ℝ)^3403 := by
    have hnat : (5428517887 : ℕ)^4427*20000000000000^3403 ≤ 9033872478389^3403*10000000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5428517887 10000000000 9033872478389 20000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1899749759/10000000000 : ℝ)^4427 ≤ (2881298457919/25000000000000 : ℝ)^3403 := by
    have hnat : (1899749759 : ℕ)^4427*25000000000000^3403 ≤ 2881298457919^3403*10000000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1899749759 10000000000 2881298457919 25000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4427/1024 : ℝ)) 4427 3403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(656936047/1250000000 : ℝ), (5428517887/10000000000 : ℝ), (-1899749759/10000000000 : ℝ)] ![(43305443758609/100000000000000 : ℝ), (9033872478389/20000000000000 : ℝ), (2881298457919/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(656936047/1250000000 : ℝ)|^4427 ≤ (43305443758609/100000000000000 : ℝ)^3403
        have hw : |(656936047/1250000000 : ℝ)|=(656936047/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5428517887/10000000000 : ℝ)|^4427 ≤ (9033872478389/20000000000000 : ℝ)^3403
        have hw : |(5428517887/10000000000 : ℝ)|=(5428517887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1899749759/10000000000 : ℝ)|^4427 ≤ (2881298457919/25000000000000 : ℝ)^3403
        have hw : |(-1899749759/10000000000 : ℝ)|=(1899749759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1465_box_11 (p : ℝ) (hpa : (4425/1024 : ℝ) ≤ p) (hpb : p ≤ (4427/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4547564497/10000000000 : ℝ)*x 0 + (4171192577/10000000000 : ℝ)*x 1 + (417119311/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4547564497/10000000000 : ℝ)^4427 ≤ (7175146504117/20000000000000 : ℝ)^3403 := by
    have hnat : (4547564497 : ℕ)^4427*20000000000000^3403 ≤ 7175146504117^3403*10000000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4547564497 10000000000 7175146504117 20000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4171192577/10000000000 : ℝ)^4427 ≤ (32062131069259/100000000000000 : ℝ)^3403 := by
    have hnat : (4171192577 : ℕ)^4427*100000000000000^3403 ≤ 32062131069259^3403*10000000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4171192577 10000000000 32062131069259 100000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (417119311/1000000000 : ℝ)^4427 ≤ (3206213639901/10000000000000 : ℝ)^3403 := by
    have hnat : (417119311 : ℕ)^4427*10000000000000^3403 ≤ 3206213639901^3403*1000000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      417119311 1000000000 3206213639901 10000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4427/1024 : ℝ)) 4427 3403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4547564497/10000000000 : ℝ), (4171192577/10000000000 : ℝ), (417119311/1000000000 : ℝ)] ![(7175146504117/20000000000000 : ℝ), (32062131069259/100000000000000 : ℝ), (3206213639901/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4547564497/10000000000 : ℝ)|^4427 ≤ (7175146504117/20000000000000 : ℝ)^3403
        have hw : |(4547564497/10000000000 : ℝ)|=(4547564497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4171192577/10000000000 : ℝ)|^4427 ≤ (32062131069259/100000000000000 : ℝ)^3403
        have hw : |(4171192577/10000000000 : ℝ)|=(4171192577/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(417119311/1000000000 : ℝ)|^4427 ≤ (3206213639901/10000000000000 : ℝ)^3403
        have hw : |(417119311/1000000000 : ℝ)|=(417119311/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1465_box_12 (p : ℝ) (hpa : (4425/1024 : ℝ) ≤ p) (hpb : p ≤ (4427/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-453107227/2500000000 : ℝ)*x 0 + (220795873/400000000 : ℝ)*x 1 + (1020859/1953125 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (453107227/2500000000 : ℝ)^4427 ≤ (677553505781/6250000000000 : ℝ)^3403 := by
    have hnat : (453107227 : ℕ)^4427*6250000000000^3403 ≤ 677553505781^3403*2500000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      453107227 2500000000 677553505781 6250000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (220795873/400000000 : ℝ)^4427 ≤ (23080497286851/50000000000000 : ℝ)^3403 := by
    have hnat : (220795873 : ℕ)^4427*50000000000000^3403 ≤ 23080497286851^3403*400000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      220795873 400000000 23080497286851 50000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1020859/1953125 : ℝ)^4427 ≤ (5374768664669/12500000000000 : ℝ)^3403 := by
    have hnat : (1020859 : ℕ)^4427*12500000000000^3403 ≤ 5374768664669^3403*1953125^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1020859 1953125 5374768664669 12500000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4427/1024 : ℝ)) 4427 3403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-453107227/2500000000 : ℝ), (220795873/400000000 : ℝ), (1020859/1953125 : ℝ)] ![(677553505781/6250000000000 : ℝ), (23080497286851/50000000000000 : ℝ), (5374768664669/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-453107227/2500000000 : ℝ)|^4427 ≤ (677553505781/6250000000000 : ℝ)^3403
        have hw : |(-453107227/2500000000 : ℝ)|=(453107227/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(220795873/400000000 : ℝ)|^4427 ≤ (23080497286851/50000000000000 : ℝ)^3403
        have hw : |(220795873/400000000 : ℝ)|=(220795873/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1020859/1953125 : ℝ)|^4427 ≤ (5374768664669/12500000000000 : ℝ)^3403
        have hw : |(1020859/1953125 : ℝ)|=(1020859/1953125 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1465_box_13 (p : ℝ) (hpa : (4425/1024 : ℝ) ≤ p) (hpb : p ≤ (4427/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2698228583/5000000000 : ℝ)*x 0 + (-991044097/5000000000 : ℝ)*x 1 + (5226798073/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2698228583/5000000000 : ℝ)^4427 ≤ (44822627991217/100000000000000 : ℝ)^3403 := by
    have hnat : (2698228583 : ℕ)^4427*100000000000000^3403 ≤ 44822627991217^3403*5000000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2698228583 5000000000 44822627991217 100000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (991044097/5000000000 : ℝ)^4427 ≤ (12179222753971/100000000000000 : ℝ)^3403 := by
    have hnat : (991044097 : ℕ)^4427*100000000000000^3403 ≤ 12179222753971^3403*5000000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      991044097 5000000000 12179222753971 100000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5226798073/10000000000 : ℝ)^4427 ≤ (21499074621219/50000000000000 : ℝ)^3403 := by
    have hnat : (5226798073 : ℕ)^4427*50000000000000^3403 ≤ 21499074621219^3403*10000000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5226798073 10000000000 21499074621219 50000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4427/1024 : ℝ)) 4427 3403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2698228583/5000000000 : ℝ), (-991044097/5000000000 : ℝ), (5226798073/10000000000 : ℝ)] ![(44822627991217/100000000000000 : ℝ), (12179222753971/100000000000000 : ℝ), (21499074621219/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2698228583/5000000000 : ℝ)|^4427 ≤ (44822627991217/100000000000000 : ℝ)^3403
        have hw : |(2698228583/5000000000 : ℝ)|=(2698228583/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-991044097/5000000000 : ℝ)|^4427 ≤ (12179222753971/100000000000000 : ℝ)^3403
        have hw : |(-991044097/5000000000 : ℝ)|=(991044097/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5226798073/10000000000 : ℝ)|^4427 ≤ (21499074621219/50000000000000 : ℝ)^3403
        have hw : |(5226798073/10000000000 : ℝ)|=(5226798073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1465_box_14 (p : ℝ) (hpa : (4425/1024 : ℝ) ≤ p) (hpb : p ≤ (4427/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1079291441/2000000000 : ℝ)*x 0 + (5226798079/10000000000 : ℝ)*x 1 + (-1982088133/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1079291441/2000000000 : ℝ)^4427 ≤ (44822628412623/100000000000000 : ℝ)^3403 := by
    have hnat : (1079291441 : ℕ)^4427*100000000000000^3403 ≤ 44822628412623^3403*2000000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1079291441 2000000000 44822628412623 100000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5226798079/10000000000 : ℝ)^4427 ≤ (859962986133/2000000000000 : ℝ)^3403 := by
    have hnat : (5226798079 : ℕ)^4427*2000000000000^3403 ≤ 859962986133^3403*10000000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5226798079 10000000000 859962986133 2000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1982088133/10000000000 : ℝ)^4427 ≤ (304480556659/2500000000000 : ℝ)^3403 := by
    have hnat : (1982088133 : ℕ)^4427*2500000000000^3403 ≤ 304480556659^3403*10000000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1982088133 10000000000 304480556659 2500000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4427/1024 : ℝ)) 4427 3403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1079291441/2000000000 : ℝ), (5226798079/10000000000 : ℝ), (-1982088133/10000000000 : ℝ)] ![(44822628412623/100000000000000 : ℝ), (859962986133/2000000000000 : ℝ), (304480556659/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1079291441/2000000000 : ℝ)|^4427 ≤ (44822628412623/100000000000000 : ℝ)^3403
        have hw : |(1079291441/2000000000 : ℝ)|=(1079291441/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5226798079/10000000000 : ℝ)|^4427 ≤ (859962986133/2000000000000 : ℝ)^3403
        have hw : |(5226798079/10000000000 : ℝ)|=(5226798079/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1982088133/10000000000 : ℝ)|^4427 ≤ (304480556659/2500000000000 : ℝ)^3403
        have hw : |(-1982088133/10000000000 : ℝ)|=(1982088133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1465_box_15 (p : ℝ) (hpa : (4425/1024 : ℝ) ≤ p) (hpb : p ≤ (4427/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (404654131/1000000000 : ℝ)*x 0 + (2210846421/5000000000 : ℝ)*x 1 + (2210846309/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (404654131/1000000000 : ℝ)^4427 ≤ (7705330109607/25000000000000 : ℝ)^3403 := by
    have hnat : (404654131 : ℕ)^4427*25000000000000^3403 ≤ 7705330109607^3403*1000000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      404654131 1000000000 7705330109607 25000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2210846421/5000000000 : ℝ)^4427 ≤ (34589340908629/100000000000000 : ℝ)^3403 := by
    have hnat : (2210846421 : ℕ)^4427*100000000000000^3403 ≤ 34589340908629^3403*5000000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2210846421 5000000000 34589340908629 100000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2210846309/5000000000 : ℝ)^4427 ≤ (17294669314539/50000000000000 : ℝ)^3403 := by
    have hnat : (2210846309 : ℕ)^4427*50000000000000^3403 ≤ 17294669314539^3403*5000000000^4427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2210846309 5000000000 17294669314539 50000000000000 4427 3403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4427/1024 : ℝ)) 4427 3403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(404654131/1000000000 : ℝ), (2210846421/5000000000 : ℝ), (2210846309/5000000000 : ℝ)] ![(7705330109607/25000000000000 : ℝ), (34589340908629/100000000000000 : ℝ), (17294669314539/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(404654131/1000000000 : ℝ)|^4427 ≤ (7705330109607/25000000000000 : ℝ)^3403
        have hw : |(404654131/1000000000 : ℝ)|=(404654131/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2210846421/5000000000 : ℝ)|^4427 ≤ (34589340908629/100000000000000 : ℝ)^3403
        have hw : |(2210846421/5000000000 : ℝ)|=(2210846421/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2210846309/5000000000 : ℝ)|^4427 ≤ (17294669314539/50000000000000 : ℝ)^3403
        have hw : |(2210846309/5000000000 : ℝ)|=(2210846309/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1465_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4425/1024 : ℝ) ≤ p) (hpb : p ≤ (4427/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79817329/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15471/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10721/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(7961/12500 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(7301/12500 : ℝ) ∧ (39899/50000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (42847/50000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15471/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10721/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15471/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10721/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15471/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10721/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15471/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10721/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15471/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10721/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15471/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10721/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10721/100000 : ℝ) ^ (4425/1024 : ℝ) ≤ (644712946618739/10000000000000000000 : ℝ) := by
    have hpowers : (10721/100000 : ℝ)^4425 ≤ (644712946618739/10000000000000000000 : ℝ)^1024 := by
      have hnat : (10721 : ℕ)^4425*10000000000000000000^1024 ≤ 644712946618739^1024*100000^4425 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10721 100000 644712946618739 10000000000000000000 4425 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10721/100000 : ℝ)) (X := (644712946618739/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4425 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15471/100000 : ℝ) ^ (4425/1024 : ℝ) ≤ (786347798556323/2500000000000000000 : ℝ) := by
    have hpowers : (15471/100000 : ℝ)^4425 ≤ (786347798556323/2500000000000000000 : ℝ)^1024 := by
      have hnat : (15471 : ℕ)^4425*2500000000000000000^1024 ≤ 786347798556323^1024*100000^4425 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15471 100000 786347798556323 2500000000000000000 4425 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15471/100000 : ℝ)) (X := (786347798556323/2500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4425 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (5000644712946618739/5000000000000000000 : ℝ) ≤ (200005967487877/200000000000000 : ℝ) ^ (4425/1024 : ℝ) := by
    have hpowers : (5000644712946618739/5000000000000000000 : ℝ)^1024 ≤ (200005967487877/200000000000000 : ℝ)^4425 := by
      have hnat : (5000644712946618739 : ℕ)^1024*200000000000000^4425 ≤ 200005967487877^4425*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5000644712946618739 5000000000000000000 200005967487877 200000000000000 1024 4425 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (200005967487877/200000000000000 : ℝ)) (X := (5000644712946618739/5000000000000000000 : ℝ)) (by norm_num) 4425 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (10003790104140844031/10000000000000000000 : ℝ) ≤ (10000876949487891/10000000000000000 : ℝ) ^ (4425/1024 : ℝ) := by
    have hpowers : (10003790104140844031/10000000000000000000 : ℝ)^1024 ≤ (10000876949487891/10000000000000000 : ℝ)^4425 := by
      have hnat : (10003790104140844031 : ℕ)^1024*10000000000000000^4425 ≤ 10000876949487891^4425*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10003790104140844031 10000000000000000000 10000876949487891 10000000000000000 1024 4425 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000876949487891/10000000000000000 : ℝ)) (X := (10003790104140844031/10000000000000000000 : ℝ)) (by norm_num) 4425 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (1250786347798556323/1250000000000000000 : ℝ) ≤ (2500363881145483/2500000000000000 : ℝ) ^ (4425/1024 : ℝ) := by
    have hpowers : (1250786347798556323/1250000000000000000 : ℝ)^1024 ≤ (2500363881145483/2500000000000000 : ℝ)^4425 := by
      have hnat : (1250786347798556323 : ℕ)^1024*2500000000000000^4425 ≤ 2500363881145483^4425*1250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1250786347798556323 1250000000000000000 2500363881145483 2500000000000000 1024 4425 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500363881145483/2500000000000000 : ℝ)) (X := (1250786347798556323/1250000000000000000 : ℝ)) (by norm_num) 4425 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(644712946618739/10000000000000000000 : ℝ) ≤ ((1249710828189588431/1250000000000000000 : ℝ)+2*(30451320739/25000000000000 : ℝ)*(10721/100000 : ℝ))^(4425/1024 : ℝ) := by
    rw [show (1249710828189588431/1250000000000000000 : ℝ)+2*(30451320739/25000000000000 : ℝ)*(10721/100000 : ℝ)=(200005967487877/200000000000000 : ℝ) by norm_num, show 1+2*(644712946618739/10000000000000000000 : ℝ)=(5000644712946618739/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(786347798556323/2500000000000000000 : ℝ)+(644712946618739/10000000000000000000 : ℝ) ≤ ((1249710828189588431/1250000000000000000 : ℝ)+(30451320739/25000000000000 : ℝ)*((15471/100000 : ℝ)+(10721/100000 : ℝ)))^(4425/1024 : ℝ) := by
    rw [show (1249710828189588431/1250000000000000000 : ℝ)+(30451320739/25000000000000 : ℝ)*((15471/100000 : ℝ)+(10721/100000 : ℝ))=(10000876949487891/10000000000000000 : ℝ) by norm_num, show 1+(786347798556323/2500000000000000000 : ℝ)+(644712946618739/10000000000000000000 : ℝ)=(10003790104140844031/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(786347798556323/2500000000000000000 : ℝ) ≤ ((1249710828189588431/1250000000000000000 : ℝ)+2*(30451320739/25000000000000 : ℝ)*(15471/100000 : ℝ))^(4425/1024 : ℝ) := by
    rw [show (1249710828189588431/1250000000000000000 : ℝ)+2*(30451320739/25000000000000 : ℝ)*(15471/100000 : ℝ)=(2500363881145483/2500000000000000 : ℝ) by norm_num, show 1+2*(786347798556323/2500000000000000000 : ℝ)=(1250786347798556323/1250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1249710828189588431/1250000000000000000 : ℝ)*(X 1 0+X 2 0)+(30451320739/25000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4425/1024 : ℝ)) (lo := (10721/100000 : ℝ)) (hi := (15471/100000 : ℝ)) (c := (1249710828189588431/1250000000000000000 : ℝ)) (alpha := (30451320739/25000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1249710828189588431/1250000000000000000 : ℝ)*(X 0 1+X 2 1)+(30451320739/25000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4425/1024 : ℝ)) (lo := (10721/100000 : ℝ)) (hi := (15471/100000 : ℝ)) (c := (1249710828189588431/1250000000000000000 : ℝ)) (alpha := (30451320739/25000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1249710828189588431/1250000000000000000 : ℝ)*(X 0 2+X 1 2)+(30451320739/25000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4425/1024 : ℝ)) (lo := (10721/100000 : ℝ)) (hi := (15471/100000 : ℝ)) (c := (1249710828189588431/1250000000000000000 : ℝ)) (alpha := (30451320739/25000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-107332351/625000000 : ℝ)*X 0 0+(1081586399/2000000000 : ℝ)*X 0 1+(5407932063/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1465_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((329367611/625000000 : ℝ)*X 1 0+(-190840473/1000000000 : ℝ)*X 1 1+(5407931789/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1465_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2634941659/5000000000 : ℝ)*X 2 0+(1351982799/2500000000 : ℝ)*X 2 1+(-1908403449/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1465_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4497561983/10000000000 : ℝ)*X 0 0+(2098392543/5000000000 : ℝ)*X 0 1+(4196787699/10000000000 : ℝ)*X 0 2+(4497561983/10000000000 : ℝ)*X 1 0+(2098392543/5000000000 : ℝ)*X 1 1+(4196787699/10000000000 : ℝ)*X 1 2+(4497561983/10000000000 : ℝ)*X 2 0+(2098392543/5000000000 : ℝ)*X 2 1+(4196787699/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1465_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-541916823/2500000000 : ℝ)*X 0 0+(2620884281/5000000000 : ℝ)*X 0 1+(163805283/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1465_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2692998831/5000000000 : ℝ)*X 1 0+(-1976168441/10000000000 : ℝ)*X 1 1+(5241768753/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1465_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5385997821/10000000000 : ℝ)*X 2 0+(5241768819/10000000000 : ℝ)*X 2 1+(-988084069/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1465_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((510575717/1250000000 : ℝ)*X 0 0+(4403123397/10000000000 : ℝ)*X 0 1+(550390487/1250000000 : ℝ)*X 0 2+(510575717/1250000000 : ℝ)*X 1 0+(4403123397/10000000000 : ℝ)*X 1 1+(550390487/1250000000 : ℝ)*X 1 2+(510575717/1250000000 : ℝ)*X 2 0+(4403123397/10000000000 : ℝ)*X 2 1+(550390487/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1465_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-32387173/156250000 : ℝ)*X 0 0+(205036099/400000000 : ℝ)*X 0 1+(1357129559/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1465_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((1313872183/2500000000 : ℝ)*X 1 0+(-474937333/2500000000 : ℝ)*X 1 1+(2714258923/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1465_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((656936047/1250000000 : ℝ)*X 2 0+(5428517887/10000000000 : ℝ)*X 2 1+(-1899749759/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1465_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4547564497/10000000000 : ℝ)*X 0 0+(4171192577/10000000000 : ℝ)*X 0 1+(417119311/1000000000 : ℝ)*X 0 2+(4547564497/10000000000 : ℝ)*X 1 0+(4171192577/10000000000 : ℝ)*X 1 1+(417119311/1000000000 : ℝ)*X 1 2+(4547564497/10000000000 : ℝ)*X 2 0+(4171192577/10000000000 : ℝ)*X 2 1+(417119311/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1465_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-453107227/2500000000 : ℝ)*X 0 0+(220795873/400000000 : ℝ)*X 0 1+(1020859/1953125 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1465_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((2698228583/5000000000 : ℝ)*X 1 0+(-991044097/5000000000 : ℝ)*X 1 1+(5226798073/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1465_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((1079291441/2000000000 : ℝ)*X 2 0+(5226798079/10000000000 : ℝ)*X 2 1+(-1982088133/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1465_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((404654131/1000000000 : ℝ)*X 0 0+(2210846421/5000000000 : ℝ)*X 0 1+(2210846309/5000000000 : ℝ)*X 0 2+(404654131/1000000000 : ℝ)*X 1 0+(2210846421/5000000000 : ℝ)*X 1 1+(2210846309/5000000000 : ℝ)*X 1 2+(404654131/1000000000 : ℝ)*X 2 0+(2210846421/5000000000 : ℝ)*X 2 1+(2210846309/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1465_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-7961/12500 : ℝ) ≤ (-159213550560786146396639811/250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (4384957/25000000000000 : ℝ)*(lower0) + (2767963/2000000000000 : ℝ)*(lower2) + (23997701/12500000000000 : ℝ)*(lower3) + (60443009/50000000000000 : ℝ)*(lower4) + (430610888715589/20000000000000 : ℝ)*(major0) + (430610888715589/20000000000000 : ℝ)*(major1) + (430610888715589/20000000000000 : ℝ)*(major2) + (595719728038583/20000000000000 : ℝ)*(sp4) + (186158167957571/6250000000000 : ℝ)*(sp5) + (372319902899889/12500000000000 : ℝ)*(sp6) + (1348691661589211/100000000000000 : ℝ)*(sp7) + (67952871779/100000000000000 : ℝ)*(sp13) + (39416993803/100000000000000 : ℝ)*(sp14) + (23529390933/50000000000000 : ℝ)*(sp15) + (1348738720371077/100000000000000 : ℝ)*(f.failure) + (595719728038583/20000000000000 : ℝ)*(f.sum) + (1453252343729/250000000000000000000000000 : ℝ)*base66 + (107719931912300859/25000000000000000000000000000000 : ℝ)*base67 + (81459525962699141/25000000000000000000000000000000 : ℝ)*base70 + (30882683587300859/25000000000000000000000000000000 : ℝ)*base71 + (1248943408979/250000000000000000000000000 : ℝ)*base74 + (80112798162300859/25000000000000000000000000000000 : ℝ)*base75 + (67065646937699141/25000000000000000000000000000000 : ℝ)*base78 + (10361441462699141/25000000000000000000000000000000 : ℝ)*base80 + (320916196979/250000000000000000000000000 : ℝ)*base82 + (4993333/5000000000000000000000 : ℝ)*base89 + (4993333/5000000000000000000000 : ℝ)*base91 + (4993333/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (7301/12500 : ℝ) ≤ (9126621453130600057404640953873/15625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (23943849/100000000000000 : ℝ)*(upper0) + (444950039/100000000000000 : ℝ)*(lower1) + (249157711/50000000000000 : ℝ)*(upper4) + (266688529/100000000000000 : ℝ)*(upper5) + (1113053578302939/50000000000000 : ℝ)*(major0) + (1113053578302939/50000000000000 : ℝ)*(major1) + (1113053578302939/50000000000000 : ℝ)*(major2) + (1519121514025149/50000000000000 : ℝ)*(sp0) + (1518993223819153/50000000000000 : ℝ)*(sp1) + (3038007195929953/100000000000000 : ℝ)*(sp2) + (697248416372013/50000000000000 : ℝ)*(sp3) + (2163325373/50000000000000 : ℝ)*(sp7) + (32072551499/12500000000000 : ℝ)*(sp9) + (117916060173/50000000000000 : ℝ)*(sp10) + (1394501159394771/100000000000000 : ℝ)*(f.failure) + (1519121514025149/50000000000000 : ℝ)*(f.sum) + (3552450301829/625000000000000000000000000 : ℝ)*base66 + (901643592693748709/62500000000000000000000000000000 : ℝ)*base67 + (509507189193748709/62500000000000000000000000000000 : ℝ)*base69 + (122965886068748709/62500000000000000000000000000000 : ℝ)*base71 + (1605468055671/625000000000000000000000000 : ℝ)*base73 + (92943820943748709/62500000000000000000000000000000 : ℝ)*base75 + (138919851693748709/62500000000000000000000000000000 : ℝ)*base77 + (62960043556251291/62500000000000000000000000000000 : ℝ)*base80 + (1292620473727/312500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (22213341/5000000000000000000000 : ℝ)*base90 + (22213341/5000000000000000000000 : ℝ)*base92 + (22213341/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (39899/50000 : ℝ) ≤ (6234415541488535728651830161967/7812500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (14493719/20000000000000 : ℝ)*(upper0) + (138071073/100000000000000 : ℝ)*(upper2) + (10388089/50000000000000 : ℝ)*(lower3) + (28216609/20000000000000 : ℝ)*(lower5) + (606288943940181/25000000000000 : ℝ)*(major0) + (606288943940181/25000000000000 : ℝ)*(major1) + (606288943940181/25000000000000 : ℝ)*(major2) + (887154129/6250000000000 : ℝ)*(sp1) + (28674093113/100000000000000 : ℝ)*(sp3) + (3676613603/50000000000000 : ℝ)*(sp4) + (330451276312857/10000000000000 : ℝ)*(sp8) + (206531620118107/6250000000000 : ℝ)*(sp9) + (51633126818059/1562500000000 : ℝ)*(sp10) + (151916258809553/10000000000000 : ℝ)*(sp11) + (1519191262188643/100000000000000 : ℝ)*(f.failure) + (51633126818059/1562500000000 : ℝ)*(f.sum) + (1039566241893/625000000000000000000000000 : ℝ)*base65 + (174440855499096011/31250000000000000000000000000000 : ℝ)*base67 + (128976690092846011/31250000000000000000000000000000 : ℝ)*base69 + (212147284030346011/31250000000000000000000000000000 : ℝ)*base71 + (9709451293741/312500000000000000000000000 : ℝ)*base74 + (184683915342846011/31250000000000000000000000000000 : ℝ)*base75 + (400844630030346011/31250000000000000000000000000000 : ℝ)*base77 + (697798419188403989/31250000000000000000000000000000 : ℝ)*base80 + (357523113143/625000000000000000000000000 : ℝ)*base81 + (21605453/5000000000000000000000 : ℝ)*base90 + (21605453/5000000000000000000000 : ℝ)*base92 + (21605453/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-42847/50000 : ℝ) ≤ (-26778662433151438444505808462903/31250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (15844191/100000000000000 : ℝ)*(lower0) + (1331809/5000000000000 : ℝ)*(upper1) + (13306087/100000000000000 : ℝ)*(lower2) + (24172249/100000000000000 : ℝ)*(upper3) + (26451443/50000000000000 : ℝ)*(upper5) + (1231555065218257/50000000000000 : ℝ)*(major0) + (1231555065218257/50000000000000 : ℝ)*(major1) + (1231555065218257/50000000000000 : ℝ)*(major2) + (10107423/20000000000000 : ℝ)*(sp4) + (1111273377/12500000000000 : ℝ)*(sp7) + (852954273448727/25000000000000 : ℝ)*(sp12) + (3411817144332023/100000000000000 : ℝ)*(sp13) + (3411817144332023/100000000000000 : ℝ)*(sp14) + (1542958132949347/100000000000000 : ℝ)*(sp15) + (1542967023136363/100000000000000 : ℝ)*(f.failure) + (3411817144332023/100000000000000 : ℝ)*(f.sum) + (1630182781827/625000000000000000000000000 : ℝ)*base66 + (873411826113334767/62500000000000000000000000000000 : ℝ)*base67 + (236511100738334767/62500000000000000000000000000000 : ℝ)*base69 + (25659206863334767/62500000000000000000000000000000 : ℝ)*base71 + (1813663616923/625000000000000000000000000 : ℝ)*base73 + (233142250800834767/62500000000000000000000000000000 : ℝ)*base75 + (111349900800834767/62500000000000000000000000000000 : ℝ)*base77 + (56971945675834767/62500000000000000000000000000000 : ℝ)*base79 + (208979775631/78125000000000000000000000 : ℝ)*base81 + (2565573/5000000000000000000000 : ℝ)*base90 + (2565573/5000000000000000000000 : ℝ)*base92 + (2565573/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1465_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4425/1024 : ℝ) ≤ p) (hpb : p ≤ (4427/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79817329/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15471/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10721/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(7961/12500 : ℝ) ≤ X j i ∧ X j i ≤ -(7301/12500 : ℝ) else (39899/50000 : ℝ) ≤ X j i ∧ X j i ≤ (42847/50000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1465_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1465_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4425/1024 : ℝ) ≤ p) (hpb : p ≤ (4427/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79817329/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15473/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10719/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(7961/12500 : ℝ) ≤ X j i ∧ X j i ≤ -(7301/12500 : ℝ) else (39899/50000 : ℝ) ≤ X j i ∧ X j i ≤ (42847/50000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1465_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1465_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4425/1024 : ℝ) ≤ p) (hpb : p ≤ (4427/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79817329/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15473/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10719/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(7961/12500 : ℝ) ≤ X j i ∧ X j i ≤ -(7301/12500 : ℝ) else (39899/50000 : ℝ) ≤ X j i ∧ X j i ≤ (42847/50000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1465_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
