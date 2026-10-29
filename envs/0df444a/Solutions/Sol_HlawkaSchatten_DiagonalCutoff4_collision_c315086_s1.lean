-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c315086_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:57:34.674351+00:00
-- url     : https://prove2.me/submissions/bc7695ec-6106-42a2-b68b-5375b54fe58f

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_ordered_majorant
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
theorem raw_linear_data {p k A : ℝ} (hp : 1 ≤ p) (X : Fin 3 → Fin 3 → ℝ)
    (h : RawFrame p k A X) :
    RawLinearData k A X (fun j => lpNorm p (X j))
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

theorem raw_linear_data_bounds {k A T : ℝ} {X : Fin 3 → Fin 3 → ℝ} {N P : Fin 3 → ℝ}
    (h : RawLinearData k A X N P T) (hA : A ≤ 3) :
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



theorem abs_signValue (b : Bool) : |signValue b|=1 := by
  cases b <;> norm_num [signValue]

theorem abs_signedPair (X : Fin 3 → Fin 3 → ℝ) (signs : Fin 3 → Fin 3 → Bool) (i h : Fin 3) :
    |signedPair X signs i h|=|pair X i h| := by
  simp [signedPair,abs_mul,abs_signValue]

theorem chart_majorant {p k A d a rho alpha beta : ℝ}
    (hp : 1 ≤ p) (ha : 0 < a) (hap : a ≤ p)
    (hrho : 0 < rho) (hrho1 : rho ≤ 1) (halpha : 0 ≤ alpha) (hbeta : 0 ≤ beta)
    (hcorner1 : 1+rho^a ≤ (1+alpha*rho)^a)
    (hcorner2 : 1+2*rho^a ≤ (1+(alpha+beta)*rho)^a)
    (X : Fin 3 → Fin 3 → ℝ) (orders : Fin 3 → Fin 3 → Fin 3)
    (signs : Fin 3 → Fin 3 → Bool) (hX : OrderedChart p k A d X orders signs)
    (i : Fin 3)
    (hratio : signedPair X signs i (orders i 1) ≤ rho*signedPair X signs i (orders i 0)) :
    lpNorm p (pair X i) ≤ signedPair X signs i (orders i 0)+
      alpha*signedPair X signs i (orders i 1)+beta*signedPair X signs i (orders i 2) := by
  obtain ⟨h2,h21,h10⟩ := hX.ordered i
  have h1 : 0 ≤ signedPair X signs i (orders i 1) := h2.trans h21
  have h0 : 0 ≤ signedPair X signs i (orders i 0) := h1.trans h10
  have hh := ordered_majorant (M := signedPair X signs i (orders i 0))
    (u := signedPair X signs i (orders i 1)) (v := signedPair X signs i (orders i 2)) hp ha hap hrho hrho1 halpha hbeta hcorner1 hcorner2 h0
    (by simpa only [abs_of_nonneg h1,abs_of_nonneg h2] using h21)
    (by simpa only [abs_of_nonneg h1] using hratio)
  have he := HlawkaSchatten.DiagonalRealBundle.lpNorm_eq3 p (pair X i)
    (i := orders i 0) (j := orders i 1) (k := orders i 2)
    ((hX.permutation i).1.ne (by decide)) ((hX.permutation i).1.ne (by decide))
    ((hX.permutation i).1.ne (by decide))
  rw [he]
  calc
    _ ≤ signedPair X signs i (orders i 0)+alpha*|signedPair X signs i (orders i 1)|+
        beta*|signedPair X signs i (orders i 2)| := by
      simpa only [abs_signedPair] using hh
    _ = _ := by rw [abs_of_nonneg h1,abs_of_nonneg h2]

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
theorem collision_support_c315086_s1_s1_0 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-19310909/500000000 : ℝ)*x 0 + (-1515132347/2500000000 : ℝ)*x 1 + (2678188121/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (19310909/500000000 : ℝ)^19 ≤ (1621765670667/100000000000000 : ℝ)^15 := by
    have hnat : (19310909 : ℕ)^19*100000000000000^15 ≤ 1621765670667^15*500000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      19310909 500000000 1621765670667 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1515132347/2500000000 : ℝ)^19 ≤ (26514496364923/50000000000000 : ℝ)^15 := by
    have hnat : (1515132347 : ℕ)^19*50000000000000^15 ≤ 26514496364923^15*2500000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1515132347 2500000000 26514496364923 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2678188121/5000000000 : ℝ)^19 ≤ (5668655198917/12500000000000 : ℝ)^15 := by
    have hnat : (2678188121 : ℕ)^19*12500000000000^15 ≤ 5668655198917^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2678188121 5000000000 5668655198917 12500000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-19310909/500000000 : ℝ), (-1515132347/2500000000 : ℝ), (2678188121/5000000000 : ℝ)] ![(1621765670667/100000000000000 : ℝ), (26514496364923/50000000000000 : ℝ), (5668655198917/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-19310909/500000000 : ℝ)|^19 ≤ (1621765670667/100000000000000 : ℝ)^15
        have hw : |(-19310909/500000000 : ℝ)|=(19310909/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1515132347/2500000000 : ℝ)|^19 ≤ (26514496364923/50000000000000 : ℝ)^15
        have hw : |(-1515132347/2500000000 : ℝ)|=(1515132347/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2678188121/5000000000 : ℝ)|^19 ≤ (5668655198917/12500000000000 : ℝ)^15
        have hw : |(2678188121/5000000000 : ℝ)|=(2678188121/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315086_s1_s1_2 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1445139991/2500000000 : ℝ)*x 0 + (-686855997/2000000000 : ℝ)*x 1 + (-3265447277/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1445139991/2500000000 : ℝ)^19 ≤ (49945368319519/100000000000000 : ℝ)^15 := by
    have hnat : (1445139991 : ℕ)^19*100000000000000^15 ≤ 49945368319519^15*2500000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1445139991 2500000000 49945368319519 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (686855997/2000000000 : ℝ)^19 ≤ (161413022237/625000000000 : ℝ)^15 := by
    have hnat : (686855997 : ℕ)^19*625000000000^15 ≤ 161413022237^15*2000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      686855997 2000000000 161413022237 625000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3265447277/10000000000 : ℝ)^19 ≤ (24228548102977/100000000000000 : ℝ)^15 := by
    have hnat : (3265447277 : ℕ)^19*100000000000000^15 ≤ 24228548102977^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3265447277 10000000000 24228548102977 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1445139991/2500000000 : ℝ), (-686855997/2000000000 : ℝ), (-3265447277/10000000000 : ℝ)] ![(49945368319519/100000000000000 : ℝ), (161413022237/625000000000 : ℝ), (24228548102977/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1445139991/2500000000 : ℝ)|^19 ≤ (49945368319519/100000000000000 : ℝ)^15
        have hw : |(1445139991/2500000000 : ℝ)|=(1445139991/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-686855997/2000000000 : ℝ)|^19 ≤ (161413022237/625000000000 : ℝ)^15
        have hw : |(-686855997/2000000000 : ℝ)|=(686855997/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3265447277/10000000000 : ℝ)|^19 ≤ (24228548102977/100000000000000 : ℝ)^15
        have hw : |(-3265447277/10000000000 : ℝ)|=(3265447277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315086_s1_s1_7 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-10053149/1000000000 : ℝ)*x 0 + (-6966819503/10000000000 : ℝ)*x 1 + (1126679939/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (10053149/1000000000 : ℝ)^19 ≤ (36854684487/12500000000000 : ℝ)^15 := by
    have hnat : (10053149 : ℕ)^19*12500000000000^15 ≤ 36854684487^15*1000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10053149 1000000000 36854684487 12500000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6966819503/10000000000 : ℝ)^19 ≤ (12653396109089/20000000000000 : ℝ)^15 := by
    have hnat : (6966819503 : ℕ)^19*20000000000000^15 ≤ 12653396109089^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6966819503 10000000000 12653396109089 20000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1126679939/2500000000 : ℝ)^19 ≤ (36438181971399/100000000000000 : ℝ)^15 := by
    have hnat : (1126679939 : ℕ)^19*100000000000000^15 ≤ 36438181971399^15*2500000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1126679939 2500000000 36438181971399 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-10053149/1000000000 : ℝ), (-6966819503/10000000000 : ℝ), (1126679939/2500000000 : ℝ)] ![(36854684487/12500000000000 : ℝ), (12653396109089/20000000000000 : ℝ), (36438181971399/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-10053149/1000000000 : ℝ)|^19 ≤ (36854684487/12500000000000 : ℝ)^15
        have hw : |(-10053149/1000000000 : ℝ)|=(10053149/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-6966819503/10000000000 : ℝ)|^19 ≤ (12653396109089/20000000000000 : ℝ)^15
        have hw : |(-6966819503/10000000000 : ℝ)|=(6966819503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1126679939/2500000000 : ℝ)|^19 ≤ (36438181971399/100000000000000 : ℝ)^15
        have hw : |(1126679939/2500000000 : ℝ)|=(1126679939/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315086_s1_s1_8 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (603069973/1000000000 : ℝ)*x 0 + (644721777/2000000000 : ℝ)*x 1 + (795992941/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (603069973/1000000000 : ℝ)^19 ≤ (52698601900131/100000000000000 : ℝ)^15 := by
    have hnat : (603069973 : ℕ)^19*100000000000000^15 ≤ 52698601900131^15*1000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      603069973 1000000000 52698601900131 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (644721777/2000000000 : ℝ)^19 ≤ (5959003555521/25000000000000 : ℝ)^15 := by
    have hnat : (644721777 : ℕ)^19*25000000000000^15 ≤ 5959003555521^15*2000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      644721777 2000000000 5959003555521 25000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (795992941/2500000000 : ℝ)^19 ≤ (2933172982687/12500000000000 : ℝ)^15 := by
    have hnat : (795992941 : ℕ)^19*12500000000000^15 ≤ 2933172982687^15*2500000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      795992941 2500000000 2933172982687 12500000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(603069973/1000000000 : ℝ), (644721777/2000000000 : ℝ), (795992941/2500000000 : ℝ)] ![(52698601900131/100000000000000 : ℝ), (5959003555521/25000000000000 : ℝ), (2933172982687/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(603069973/1000000000 : ℝ)|^19 ≤ (52698601900131/100000000000000 : ℝ)^15
        have hw : |(603069973/1000000000 : ℝ)|=(603069973/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(644721777/2000000000 : ℝ)|^19 ≤ (5959003555521/25000000000000 : ℝ)^15
        have hw : |(644721777/2000000000 : ℝ)|=(644721777/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(795992941/2500000000 : ℝ)|^19 ≤ (2933172982687/12500000000000 : ℝ)^15
        have hw : |(795992941/2500000000 : ℝ)|=(795992941/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315086_s1_s1_9 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (5917419691/10000000000 : ℝ)*x 0 + (-826343853/2500000000 : ℝ)*x 1 + (-3235526021/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5917419691/10000000000 : ℝ)^19 ≤ (12861975576833/25000000000000 : ℝ)^15 := by
    have hnat : (5917419691 : ℕ)^19*25000000000000^15 ≤ 12861975576833^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5917419691 10000000000 12861975576833 25000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (826343853/2500000000 : ℝ)^19 ≤ (24604412720781/100000000000000 : ℝ)^15 := by
    have hnat : (826343853 : ℕ)^19*100000000000000^15 ≤ 24604412720781^15*2500000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      826343853 2500000000 24604412720781 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3235526021/10000000000 : ℝ)^19 ≤ (5986921237811/25000000000000 : ℝ)^15 := by
    have hnat : (3235526021 : ℕ)^19*25000000000000^15 ≤ 5986921237811^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3235526021 10000000000 5986921237811 25000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5917419691/10000000000 : ℝ), (-826343853/2500000000 : ℝ), (-3235526021/10000000000 : ℝ)] ![(12861975576833/25000000000000 : ℝ), (24604412720781/100000000000000 : ℝ), (5986921237811/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5917419691/10000000000 : ℝ)|^19 ≤ (12861975576833/25000000000000 : ℝ)^15
        have hw : |(5917419691/10000000000 : ℝ)|=(5917419691/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-826343853/2500000000 : ℝ)|^19 ≤ (24604412720781/100000000000000 : ℝ)^15
        have hw : |(-826343853/2500000000 : ℝ)|=(826343853/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3235526021/10000000000 : ℝ)|^19 ≤ (5986921237811/25000000000000 : ℝ)^15
        have hw : |(-3235526021/10000000000 : ℝ)|=(3235526021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315086_s1_s1_13 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (181361051/625000000 : ℝ)*x 0 + (-1284332199/10000000000 : ℝ)*x 1 + (7690772783/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (181361051/625000000 : ℝ)^19 ≤ (20862887120419/100000000000000 : ℝ)^15 := by
    have hnat : (181361051 : ℕ)^19*100000000000000^15 ≤ 20862887120419^15*625000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      181361051 625000000 20862887120419 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1284332199/10000000000 : ℝ)^19 ≤ (928755394417/12500000000000 : ℝ)^15 := by
    have hnat : (1284332199 : ℕ)^19*12500000000000^15 ≤ 928755394417^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1284332199 10000000000 928755394417 12500000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7690772783/10000000000 : ℝ)^19 ≤ (71707069713113/100000000000000 : ℝ)^15 := by
    have hnat : (7690772783 : ℕ)^19*100000000000000^15 ≤ 71707069713113^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7690772783 10000000000 71707069713113 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(181361051/625000000 : ℝ), (-1284332199/10000000000 : ℝ), (7690772783/10000000000 : ℝ)] ![(20862887120419/100000000000000 : ℝ), (928755394417/12500000000000 : ℝ), (71707069713113/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(181361051/625000000 : ℝ)|^19 ≤ (20862887120419/100000000000000 : ℝ)^15
        have hw : |(181361051/625000000 : ℝ)|=(181361051/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1284332199/10000000000 : ℝ)|^19 ≤ (928755394417/12500000000000 : ℝ)^15
        have hw : |(-1284332199/10000000000 : ℝ)|=(1284332199/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(7690772783/10000000000 : ℝ)|^19 ≤ (71707069713113/100000000000000 : ℝ)^15
        have hw : |(7690772783/10000000000 : ℝ)|=(7690772783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315086_s1_s1_14 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-33/5000000000 : ℝ)*x 0 + (-5854499529/10000000000 : ℝ)*x 1 + (2858191511/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (33/5000000000 : ℝ)^19 ≤ (2173/50000000000000 : ℝ)^15 := by
    have hnat : (33 : ℕ)^19*50000000000000^15 ≤ 2173^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33 5000000000 2173 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5854499529/10000000000 : ℝ)^19 ≤ (10151192055791/20000000000000 : ℝ)^15 := by
    have hnat : (5854499529 : ℕ)^19*20000000000000^15 ≤ 10151192055791^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5854499529 10000000000 10151192055791 20000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2858191511/5000000000 : ℝ)^19 ≤ (24622019855163/50000000000000 : ℝ)^15 := by
    have hnat : (2858191511 : ℕ)^19*50000000000000^15 ≤ 24622019855163^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2858191511 5000000000 24622019855163 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-33/5000000000 : ℝ), (-5854499529/10000000000 : ℝ), (2858191511/5000000000 : ℝ)] ![(2173/50000000000000 : ℝ), (10151192055791/20000000000000 : ℝ), (24622019855163/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-33/5000000000 : ℝ)|^19 ≤ (2173/50000000000000 : ℝ)^15
        have hw : |(-33/5000000000 : ℝ)|=(33/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-5854499529/10000000000 : ℝ)|^19 ≤ (10151192055791/20000000000000 : ℝ)^15
        have hw : |(-5854499529/10000000000 : ℝ)|=(5854499529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2858191511/5000000000 : ℝ)|^19 ≤ (24622019855163/50000000000000 : ℝ)^15
        have hw : |(2858191511/5000000000 : ℝ)|=(2858191511/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315086_s1_s1_15 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1306086767/2000000000 : ℝ)*x 0 + (608009099/2000000000 : ℝ)*x 1 + (344998061/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1306086767/2000000000 : ℝ)^19 ≤ (29144945459391/50000000000000 : ℝ)^15 := by
    have hnat : (1306086767 : ℕ)^19*50000000000000^15 ≤ 29144945459391^15*2000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1306086767 2000000000 29144945459391 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (608009099/2000000000 : ℝ)^19 ≤ (11065000624477/50000000000000 : ℝ)^15 := by
    have hnat : (608009099 : ℕ)^19*50000000000000^15 ≤ 11065000624477^15*2000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      608009099 2000000000 11065000624477 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (344998061/1250000000 : ℝ)^19 ≤ (19580107814883/100000000000000 : ℝ)^15 := by
    have hnat : (344998061 : ℕ)^19*100000000000000^15 ≤ 19580107814883^15*1250000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      344998061 1250000000 19580107814883 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1306086767/2000000000 : ℝ), (608009099/2000000000 : ℝ), (344998061/1250000000 : ℝ)] ![(29144945459391/50000000000000 : ℝ), (11065000624477/50000000000000 : ℝ), (19580107814883/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1306086767/2000000000 : ℝ)|^19 ≤ (29144945459391/50000000000000 : ℝ)^15
        have hw : |(1306086767/2000000000 : ℝ)|=(1306086767/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(608009099/2000000000 : ℝ)|^19 ≤ (11065000624477/50000000000000 : ℝ)^15
        have hw : |(608009099/2000000000 : ℝ)|=(608009099/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(344998061/1250000000 : ℝ)|^19 ≤ (19580107814883/100000000000000 : ℝ)^15
        have hw : |(344998061/1250000000 : ℝ)|=(344998061/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315086_s1_s1_16 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1548490143/2500000000 : ℝ)*x 0 + (-3316095031/10000000000 : ℝ)*x 1 + (-72323149/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1548490143/2500000000 : ℝ)^19 ≤ (5451215522661/10000000000000 : ℝ)^15 := by
    have hnat : (1548490143 : ℕ)^19*10000000000000^15 ≤ 5451215522661^15*2500000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1548490143 2500000000 5451215522661 10000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3316095031/10000000000 : ℝ)^19 ≤ (2470552909947/10000000000000 : ℝ)^15 := by
    have hnat : (3316095031 : ℕ)^19*10000000000000^15 ≤ 2470552909947^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3316095031 10000000000 2470552909947 10000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (72323149/250000000 : ℝ)^19 ≤ (2078231566123/10000000000000 : ℝ)^15 := by
    have hnat : (72323149 : ℕ)^19*10000000000000^15 ≤ 2078231566123^15*250000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      72323149 250000000 2078231566123 10000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1548490143/2500000000 : ℝ), (-3316095031/10000000000 : ℝ), (-72323149/250000000 : ℝ)] ![(5451215522661/10000000000000 : ℝ), (2470552909947/10000000000000 : ℝ), (2078231566123/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1548490143/2500000000 : ℝ)|^19 ≤ (5451215522661/10000000000000 : ℝ)^15
        have hw : |(1548490143/2500000000 : ℝ)|=(1548490143/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3316095031/10000000000 : ℝ)|^19 ≤ (2470552909947/10000000000000 : ℝ)^15
        have hw : |(-3316095031/10000000000 : ℝ)|=(3316095031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-72323149/250000000 : ℝ)|^19 ≤ (2078231566123/10000000000000 : ℝ)^15
        have hw : |(-72323149/250000000 : ℝ)|=(72323149/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315086_s1_s1_20 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (3207594593/10000000000 : ℝ)*x 0 + (-314211729/1250000000 : ℝ)*x 1 + (6586104813/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3207594593/10000000000 : ℝ)^19 ≤ (23686124013093/100000000000000 : ℝ)^15 := by
    have hnat : (3207594593 : ℕ)^19*100000000000000^15 ≤ 23686124013093^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3207594593 10000000000 23686124013093 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (314211729/1250000000 : ℝ)^19 ≤ (17393848404817/100000000000000 : ℝ)^15 := by
    have hnat : (314211729 : ℕ)^19*100000000000000^15 ≤ 17393848404817^15*1250000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      314211729 1250000000 17393848404817 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6586104813/10000000000 : ℝ)^19 ≤ (29460013782449/50000000000000 : ℝ)^15 := by
    have hnat : (6586104813 : ℕ)^19*50000000000000^15 ≤ 29460013782449^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6586104813 10000000000 29460013782449 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3207594593/10000000000 : ℝ), (-314211729/1250000000 : ℝ), (6586104813/10000000000 : ℝ)] ![(23686124013093/100000000000000 : ℝ), (17393848404817/100000000000000 : ℝ), (29460013782449/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3207594593/10000000000 : ℝ)|^19 ≤ (23686124013093/100000000000000 : ℝ)^15
        have hw : |(3207594593/10000000000 : ℝ)|=(3207594593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-314211729/1250000000 : ℝ)|^19 ≤ (17393848404817/100000000000000 : ℝ)^15
        have hw : |(-314211729/1250000000 : ℝ)|=(314211729/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6586104813/10000000000 : ℝ)|^19 ≤ (29460013782449/50000000000000 : ℝ)^15
        have hw : |(6586104813/10000000000 : ℝ)|=(6586104813/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315086_s1_s1_21 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (9071/5000000000 : ℝ)*x 0 + (-321279893/500000000 : ℝ)*x 1 + (1025197429/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (9071/5000000000 : ℝ)^19 ≤ (2670779/50000000000000 : ℝ)^15 := by
    have hnat : (9071 : ℕ)^19*50000000000000^15 ≤ 2670779^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9071 5000000000 2670779 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (321279893/500000000 : ℝ)^19 ≤ (57107150000511/100000000000000 : ℝ)^15 := by
    have hnat : (321279893 : ℕ)^19*100000000000000^15 ≤ 57107150000511^15*500000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      321279893 500000000 57107150000511 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1025197429/2000000000 : ℝ)^19 ≤ (5361605579747/12500000000000 : ℝ)^15 := by
    have hnat : (1025197429 : ℕ)^19*12500000000000^15 ≤ 5361605579747^15*2000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1025197429 2000000000 5361605579747 12500000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(9071/5000000000 : ℝ), (-321279893/500000000 : ℝ), (1025197429/2000000000 : ℝ)] ![(2670779/50000000000000 : ℝ), (57107150000511/100000000000000 : ℝ), (5361605579747/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(9071/5000000000 : ℝ)|^19 ≤ (2670779/50000000000000 : ℝ)^15
        have hw : |(9071/5000000000 : ℝ)|=(9071/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-321279893/500000000 : ℝ)|^19 ≤ (57107150000511/100000000000000 : ℝ)^15
        have hw : |(-321279893/500000000 : ℝ)|=(321279893/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1025197429/2000000000 : ℝ)|^19 ≤ (5361605579747/12500000000000 : ℝ)^15
        have hw : |(1025197429/2000000000 : ℝ)|=(1025197429/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315086_s1_s1_22 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (6530452377/10000000000 : ℝ)*x 0 + (1492397991/5000000000 : ℝ)*x 1 + (1408181163/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6530452377/10000000000 : ℝ)^19 ≤ (58290100556919/100000000000000 : ℝ)^15 := by
    have hnat : (6530452377 : ℕ)^19*100000000000000^15 ≤ 58290100556919^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6530452377 10000000000 58290100556919 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1492397991/5000000000 : ℝ)^19 ≤ (1351362642949/6250000000000 : ℝ)^15 := by
    have hnat : (1492397991 : ℕ)^19*6250000000000^15 ≤ 1351362642949^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1492397991 5000000000 1351362642949 6250000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1408181163/5000000000 : ℝ)^19 ≤ (2008809714129/10000000000000 : ℝ)^15 := by
    have hnat : (1408181163 : ℕ)^19*10000000000000^15 ≤ 2008809714129^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1408181163 5000000000 2008809714129 10000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6530452377/10000000000 : ℝ), (1492397991/5000000000 : ℝ), (1408181163/5000000000 : ℝ)] ![(58290100556919/100000000000000 : ℝ), (1351362642949/6250000000000 : ℝ), (2008809714129/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6530452377/10000000000 : ℝ)|^19 ≤ (58290100556919/100000000000000 : ℝ)^15
        have hw : |(6530452377/10000000000 : ℝ)|=(6530452377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1492397991/5000000000 : ℝ)|^19 ≤ (1351362642949/6250000000000 : ℝ)^15
        have hw : |(1492397991/5000000000 : ℝ)|=(1492397991/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1408181163/5000000000 : ℝ)|^19 ≤ (2008809714129/10000000000000 : ℝ)^15
        have hw : |(1408181163/5000000000 : ℝ)|=(1408181163/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315086_s1_s1_23 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1134721829/2000000000 : ℝ)*x 0 + (-3544189813/10000000000 : ℝ)*x 1 + (-1638903983/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1134721829/2000000000 : ℝ)^19 ≤ (4877776806469/10000000000000 : ℝ)^15 := by
    have hnat : (1134721829 : ℕ)^19*10000000000000^15 ≤ 4877776806469^15*2000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1134721829 2000000000 4877776806469 10000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3544189813/10000000000 : ℝ)^19 ≤ (6719364095639/25000000000000 : ℝ)^15 := by
    have hnat : (3544189813 : ℕ)^19*25000000000000^15 ≤ 6719364095639^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3544189813 10000000000 6719364095639 25000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1638903983/5000000000 : ℝ)^19 ≤ (6086193885499/25000000000000 : ℝ)^15 := by
    have hnat : (1638903983 : ℕ)^19*25000000000000^15 ≤ 6086193885499^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1638903983 5000000000 6086193885499 25000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1134721829/2000000000 : ℝ), (-3544189813/10000000000 : ℝ), (-1638903983/5000000000 : ℝ)] ![(4877776806469/10000000000000 : ℝ), (6719364095639/25000000000000 : ℝ), (6086193885499/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1134721829/2000000000 : ℝ)|^19 ≤ (4877776806469/10000000000000 : ℝ)^15
        have hw : |(1134721829/2000000000 : ℝ)|=(1134721829/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3544189813/10000000000 : ℝ)|^19 ≤ (6719364095639/25000000000000 : ℝ)^15
        have hw : |(-3544189813/10000000000 : ℝ)|=(3544189813/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1638903983/5000000000 : ℝ)|^19 ≤ (6086193885499/25000000000000 : ℝ)^15
        have hw : |(-1638903983/5000000000 : ℝ)|=(1638903983/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315086_s1_s1_27 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (4504921851/10000000000 : ℝ)*x 0 + (-2633694851/10000000000 : ℝ)*x 1 + (2667866247/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4504921851/10000000000 : ℝ)^19 ≤ (36419769922241/100000000000000 : ℝ)^15 := by
    have hnat : (4504921851 : ℕ)^19*100000000000000^15 ≤ 36419769922241^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4504921851 10000000000 36419769922241 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633694851/10000000000 : ℝ)^19 ≤ (9226130224291/50000000000000 : ℝ)^15 := by
    have hnat : (2633694851 : ℕ)^19*50000000000000^15 ≤ 9226130224291^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633694851 10000000000 9226130224291 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2667866247/5000000000 : ℝ)^19 ≤ (45127969620677/100000000000000 : ℝ)^15 := by
    have hnat : (2667866247 : ℕ)^19*100000000000000^15 ≤ 45127969620677^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2667866247 5000000000 45127969620677 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4504921851/10000000000 : ℝ), (-2633694851/10000000000 : ℝ), (2667866247/5000000000 : ℝ)] ![(36419769922241/100000000000000 : ℝ), (9226130224291/50000000000000 : ℝ), (45127969620677/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4504921851/10000000000 : ℝ)|^19 ≤ (36419769922241/100000000000000 : ℝ)^15
        have hw : |(4504921851/10000000000 : ℝ)|=(4504921851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2633694851/10000000000 : ℝ)|^19 ≤ (9226130224291/50000000000000 : ℝ)^15
        have hw : |(-2633694851/10000000000 : ℝ)|=(2633694851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2667866247/5000000000 : ℝ)|^19 ≤ (45127969620677/100000000000000 : ℝ)^15
        have hw : |(2667866247/5000000000 : ℝ)|=(2667866247/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c315086_s1 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (174659/100000 : ℝ) (34911/20000 : ℝ) (15821/20000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]])
    (hprev0 : (0 : ℝ) ≤ ((17313/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(17313/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-80217/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-80217/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(40159/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(40159/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((11297/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(11297/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-51663/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-51663/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(43753/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(43753/100000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (15821/20000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (15821/20000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (15821/20000 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (15821/20000 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (15821/20000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (15821/20000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base13 : ((1 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 2).2]
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
  have base17 : ((1 : ℝ)*X 1 1+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 1).2]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base50 : ((1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 2+(1 : ℝ)*X 2 0+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base60 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 1+(-1 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.2.1]
  have base62 : ((-1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).1]
  have base63 : ((1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).2]
  have base64 : ((-1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).1]
  have base65 : ((1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).2]
  have base66 : ((-1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).1]
  have base67 : ((1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).2]
  have base68 : ((-1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).1]
  have base69 : ((1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).2]
  have base70 : ((-1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).1]
  have base71 : ((1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).2]
  have base72 : ((-1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).1]
  have base73 : ((1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).2]
  have base74 : ((-1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).1]
  have base75 : ((1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).2]
  have base76 : ((-1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).1]
  have base77 : ((1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).2]
  have base78 : ((-1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).1]
  have base79 : ((1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).2]
  have base80 : ((-1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).1]
  have base81 : ((1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).2]
  have base82 : ((-1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).1]
  have base83 : ((1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).2]
  have base84 : ((-1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).1]
  have base85 : ((1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).2]
  have base86 : ((-1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).1]
  have base87 : ((1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).2]
  have base88 : ((-1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).1]
  have base89 : ((1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).2]
  have base90 : ((-1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).1]
  have base91 : ((1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).2]
  have base92 : ((-1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.1]
  have base93 : ((1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.2]
  rcases hprev0 with ⟨ratio_s0_0,ratio_s0_1,ratio_s0_2⟩
  have s1_pow0 : (17313/25000 : ℝ) ^ (75/16 : ℝ) ≤ (8932982969246418279/50000000000000000000 : ℝ) := by
    have hpowers : (17313/25000 : ℝ)^75 ≤ (8932982969246418279/50000000000000000000 : ℝ)^16 := by
      have hnat : (17313 : ℕ)^75*50000000000000000000^16 ≤ 8932982969246418279^16*25000^75 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17313 25000 8932982969246418279 50000000000000000000 75 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (17313/25000 : ℝ)) (X := (8932982969246418279/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (58932982969246418279/50000000000000000000 : ℝ) ≤ (10356893955911749/10000000000000000 : ℝ) ^ (75/16 : ℝ) := by
    have hpowers : (58932982969246418279/50000000000000000000 : ℝ)^16 ≤ (10356893955911749/10000000000000000 : ℝ)^75 := by
      have hnat : (58932982969246418279 : ℕ)^16*10000000000000000^75 ≤ 10356893955911749^75*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        58932982969246418279 50000000000000000000 10356893955911749 10000000000000000 16 75 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10356893955911749/10000000000000000 : ℝ)) (X := (58932982969246418279/50000000000000000000 : ℝ)) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (33932982969246418279/25000000000000000000 : ℝ) ≤ (5336733354376449/5000000000000000 : ℝ) ^ (75/16 : ℝ) := by
    have hpowers : (33932982969246418279/25000000000000000000 : ℝ)^16 ≤ (5336733354376449/5000000000000000 : ℝ)^75 := by
      have hnat : (33932982969246418279 : ℕ)^16*5000000000000000^75 ≤ 5336733354376449^75*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        33932982969246418279 25000000000000000000 5336733354376449 5000000000000000 16 75 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5336733354376449/5000000000000000 : ℝ)) (X := (33932982969246418279/25000000000000000000 : ℝ)) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(118964651970583/2308400000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(316572752841149/6925200000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (75/16 : ℝ)) (rho := (17313/25000 : ℝ)) (alpha := (118964651970583/2308400000000000 : ℝ)) (beta := (316572752841149/6925200000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (17313/25000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(118964651970583/2308400000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(316572752841149/6925200000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (80217/100000 : ℝ) ^ (75/16 : ℝ) ≤ (35583513247597430923/100000000000000000000 : ℝ) := by
    have hpowers : (80217/100000 : ℝ)^75 ≤ (35583513247597430923/100000000000000000000 : ℝ)^16 := by
      have hnat : (80217 : ℕ)^75*100000000000000000000^16 ≤ 35583513247597430923^16*100000^75 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        80217 100000 35583513247597430923 100000000000000000000 75 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (80217/100000 : ℝ)) (X := (35583513247597430923/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (135583513247597430923/100000000000000000000 : ℝ) ≤ (2667743950491599/2500000000000000 : ℝ) ^ (75/16 : ℝ) := by
    have hpowers : (135583513247597430923/100000000000000000000 : ℝ)^16 ≤ (2667743950491599/2500000000000000 : ℝ)^75 := by
      have hnat : (135583513247597430923 : ℕ)^16*2500000000000000^75 ≤ 2667743950491599^75*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        135583513247597430923 100000000000000000000 2667743950491599 2500000000000000 16 75 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2667743950491599/2500000000000000 : ℝ)) (X := (135583513247597430923/100000000000000000000 : ℝ)) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (85583513247597430923/50000000000000000000 : ℝ) ≤ (1401865353028271/1250000000000000 : ℝ) ^ (75/16 : ℝ) := by
    have hpowers : (85583513247597430923/50000000000000000000 : ℝ)^16 ≤ (1401865353028271/1250000000000000 : ℝ)^75 := by
      have hnat : (85583513247597430923 : ℕ)^16*1250000000000000^75 ≤ 1401865353028271^75*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        85583513247597430923 50000000000000000000 1401865353028271 1250000000000000 16 75 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1401865353028271/1250000000000000 : ℝ)) (X := (85583513247597430923/50000000000000000000 : ℝ)) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(167743950491599/2005425000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2))+(135986755564943/2005425000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (75/16 : ℝ)) (rho := (80217/100000 : ℝ)) (alpha := (167743950491599/2005425000000000 : ℝ)) (beta := (135986755564943/2005425000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 2) ≤ (80217/100000 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(167743950491599/2005425000000000 : ℝ)*((1 : ℝ)*pair X 1 2)+(135986755564943/2005425000000000 : ℝ)*((1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (40159/50000 : ℝ) ^ (75/16 : ℝ) ≤ (17897006894600881709/50000000000000000000 : ℝ) := by
    have hpowers : (40159/50000 : ℝ)^75 ≤ (17897006894600881709/50000000000000000000 : ℝ)^16 := by
      have hnat : (40159 : ℕ)^75*50000000000000000000^16 ≤ 17897006894600881709^16*50000^75 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        40159 50000 17897006894600881709 50000000000000000000 75 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (40159/50000 : ℝ)) (X := (17897006894600881709/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (67897006894600881709/50000000000000000000 : ℝ) ≤ (5337253996329913/5000000000000000 : ℝ) ^ (75/16 : ℝ) := by
    have hpowers : (67897006894600881709/50000000000000000000 : ℝ)^16 ≤ (5337253996329913/5000000000000000 : ℝ)^75 := by
      have hnat : (67897006894600881709 : ℕ)^16*5000000000000000^75 ≤ 5337253996329913^75*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        67897006894600881709 50000000000000000000 5337253996329913 5000000000000000 16 75 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5337253996329913/5000000000000000 : ℝ)) (X := (67897006894600881709/50000000000000000000 : ℝ)) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (42897006894600881709/25000000000000000000 : ℝ) ≤ (11220801755369777/10000000000000000 : ℝ) ^ (75/16 : ℝ) := by
    have hpowers : (42897006894600881709/25000000000000000000 : ℝ)^16 ≤ (11220801755369777/10000000000000000 : ℝ)^75 := by
      have hnat : (42897006894600881709 : ℕ)^16*10000000000000000^75 ≤ 11220801755369777^75*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        42897006894600881709 25000000000000000000 11220801755369777 10000000000000000 16 75 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11220801755369777/10000000000000000 : ℝ)) (X := (42897006894600881709/25000000000000000000 : ℝ)) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(337253996329913/4015900000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(546293762709951/8031800000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (75/16 : ℝ)) (rho := (40159/50000 : ℝ)) (alpha := (337253996329913/4015900000000000 : ℝ)) (beta := (546293762709951/8031800000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (40159/50000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(337253996329913/4015900000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(546293762709951/8031800000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-19310909/500000000 : ℝ)*X 0 0+(-1515132347/2500000000 : ℝ)*X 0 1+(2678188121/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c315086_s1_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((1445139991/2500000000 : ℝ)*X 2 0+(-686855997/2000000000 : ℝ)*X 2 1+(-3265447277/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c315086_s1_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-10053149/1000000000 : ℝ)*X 0 0+(-6966819503/10000000000 : ℝ)*X 0 1+(1126679939/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c315086_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((603069973/1000000000 : ℝ)*X 1 0+(644721777/2000000000 : ℝ)*X 1 1+(795992941/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c315086_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((5917419691/10000000000 : ℝ)*X 2 0+(-826343853/2500000000 : ℝ)*X 2 1+(-3235526021/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c315086_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((181361051/625000000 : ℝ)*X 0 0+(-1284332199/10000000000 : ℝ)*X 0 1+(7690772783/10000000000 : ℝ)*X 0 2+(181361051/625000000 : ℝ)*X 1 0+(-1284332199/10000000000 : ℝ)*X 1 1+(7690772783/10000000000 : ℝ)*X 1 2+(181361051/625000000 : ℝ)*X 2 0+(-1284332199/10000000000 : ℝ)*X 2 1+(7690772783/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c315086_s1_s1_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((-33/5000000000 : ℝ)*X 0 0+(-5854499529/10000000000 : ℝ)*X 0 1+(2858191511/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c315086_s1_s1_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((1306086767/2000000000 : ℝ)*X 1 0+(608009099/2000000000 : ℝ)*X 1 1+(344998061/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c315086_s1_s1_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_16 : ((1548490143/2500000000 : ℝ)*X 2 0+(-3316095031/10000000000 : ℝ)*X 2 1+(-72323149/250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c315086_s1_s1_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((3207594593/10000000000 : ℝ)*X 0 0+(-314211729/1250000000 : ℝ)*X 0 1+(6586104813/10000000000 : ℝ)*X 0 2+(3207594593/10000000000 : ℝ)*X 1 0+(-314211729/1250000000 : ℝ)*X 1 1+(6586104813/10000000000 : ℝ)*X 1 2+(3207594593/10000000000 : ℝ)*X 2 0+(-314211729/1250000000 : ℝ)*X 2 1+(6586104813/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c315086_s1_s1_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((9071/5000000000 : ℝ)*X 0 0+(-321279893/500000000 : ℝ)*X 0 1+(1025197429/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c315086_s1_s1_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_22 : ((6530452377/10000000000 : ℝ)*X 1 0+(1492397991/5000000000 : ℝ)*X 1 1+(1408181163/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c315086_s1_s1_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_23 : ((1134721829/2000000000 : ℝ)*X 2 0+(-3544189813/10000000000 : ℝ)*X 2 1+(-1638903983/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c315086_s1_s1_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_27 : ((4504921851/10000000000 : ℝ)*X 0 0+(-2633694851/10000000000 : ℝ)*X 0 1+(2667866247/5000000000 : ℝ)*X 0 2+(4504921851/10000000000 : ℝ)*X 1 0+(-2633694851/10000000000 : ℝ)*X 1 1+(2667866247/5000000000 : ℝ)*X 1 2+(4504921851/10000000000 : ℝ)*X 2 0+(-2633694851/10000000000 : ℝ)*X 2 1+(2667866247/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c315086_s1_s1_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((11297/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(11297/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (8158766508609028694494411/927030356000000000000000000000 : ℝ) := by norm_num
    linear_combination (849811/1000000000000 : ℝ)*(base17) + (598242159197/1000000000000 : ℝ)*(base40) + (1048199/1000000000000 : ℝ)*(base50) + (3183759/1000000000000 : ℝ)*(base60) + (792973457029/200000000000 : ℝ)*(major_s1_0) + (792973457029/200000000000 : ℝ)*(major_s1_1) + (792973457029/200000000000 : ℝ)*(major_s1_2) + (352132259/1000000000000 : ℝ)*(sp_s1_2) + (2829783858297/500000000000 : ℝ)*(sp_s1_7) + (5659668960549/1000000000000 : ℝ)*(sp_s1_8) + (2829658839051/500000000000 : ℝ)*(sp_s1_9) + (2270026867041/1000000000000 : ℝ)*(sp_s1_13) + (34959229/1000000000000 : ℝ)*(sp_s1_20) + (102093767/1000000000000 : ℝ)*(sp_s1_21) + (227006182627/100000000000 : ℝ)*(f.failure) + (141491745259/25000000000 : ℝ)*(f.sum) + (5169185344631695441/64428690060000000000000000000000 : ℝ)*base62 + (913816339959/64254400000000000000000000 : ℝ)*base64 + (252021927232561/802170000000000000000000000 : ℝ)*base66 + (22562589834837/803180000000000000000000000 : ℝ)*base68 + (777404081583700341/18540607120000000000000000000000 : ℝ)*base70 + (388041846709457/1385040000000000000000000000 : ℝ)*base73 + (11990299864507/802170000000000000000000000 : ℝ)*base75 + (370521273253/18467200000000000000000000 : ℝ)*base76 + (590940913988647951/7406916912000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base81 + (1/1000000000000 : ℝ)*base85 + (807/10000000000000000 : ℝ)*base86 + (807/10000000000000000 : ℝ)*base88 + (807/10000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((-51663/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-51663/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (3967430268031614564798663523577/413131078151400000000000000000000000 : ℝ) := by norm_num
    linear_combination (479299/125000000000 : ℝ)*(base13) + (2881417/500000000000 : ℝ)*(base15) + (100396986179/40000000000 : ℝ)*(base40) + (291153075043/1000000000000 : ℝ)*(base60) + (9138502415831/1000000000000 : ℝ)*(major_s1_0) + (9138502415831/1000000000000 : ℝ)*(major_s1_1) + (9138502415831/1000000000000 : ℝ)*(major_s1_2) + (11348221/250000000000 : ℝ)*(sp_s1_13) + (13044801106701/1000000000000 : ℝ)*(sp_s1_14) + (13044488108067/1000000000000 : ℝ)*(sp_s1_15) + (13044804941093/1000000000000 : ℝ)*(sp_s1_16) + (81751972653/15625000000 : ℝ)*(sp_s1_20) + (19441887/62500000000 : ℝ)*(sp_s1_22) + (12523389/500000000000 : ℝ)*(sp_s1_27) + (5232196689453/1000000000000 : ℝ)*(f.failure) + (13044804941093/1000000000000 : ℝ)*(f.sum) + (292567644324595023221/322143450300000000000000000000000 : ℝ)*base62 + (3047691967244779/8031800000000000000000000000 : ℝ)*base65 + (1033443516249833/1002712500000000000000000000 : ℝ)*base66 + (4596282239084427/4015900000000000000000000000 : ℝ)*base68 + (1859269261113987971/18540607120000000000000000000000 : ℝ)*base70 + (9225900404223941/6925200000000000000000000000 : ℝ)*base72 + (202204839457939/250678125000000000000000000 : ℝ)*base74 + (1664375651539113/2308400000000000000000000000 : ℝ)*base77 + (6924140402981333159/7406916912000000000000000000000 : ℝ)*base78 + (71527/100000000000000000 : ℝ)*base87 + (71527/100000000000000000 : ℝ)*base89 + (71527/100000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(43753/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(43753/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (604460682240496124679692052251/61969661722710000000000000000000000 : ℝ) := by norm_num
    linear_combination (3939051/1000000000000 : ℝ)*(base15) + (171799182843/62500000000 : ℝ)*(base40) + (882049/500000000000 : ℝ)*(base50) + (235537665367/25000000000 : ℝ)*(major_s1_0) + (235537665367/25000000000 : ℝ)*(major_s1_1) + (235537665367/25000000000 : ℝ)*(major_s1_2) + (35179811/1000000000000 : ℝ)*(sp_s1_0) + (30638443/250000000000 : ℝ)*(sp_s1_2) + (3856409/62500000000 : ℝ)*(sp_s1_7) + (120753171/250000000000 : ℝ)*(sp_s1_15) + (6724341994687/500000000000 : ℝ)*(sp_s1_21) + (13448293919993/1000000000000 : ℝ)*(sp_s1_22) + (3362164579489/250000000000 : ℝ)*(sp_s1_23) + (5394229106247/1000000000000 : ℝ)*(sp_s1_27) + (5394229106247/1000000000000 : ℝ)*(f.failure) + (840548804483/62500000000 : ℝ)*(f.sum) + (15185041782919319897/32214345030000000000000000000000 : ℝ)*base63 + (264682788892749/401590000000000000000000000 : ℝ)*base65 + (76612761839063/80217000000000000000000000 : ℝ)*base66 + (29420777980151/200795000000000000000000000 : ℝ)*base69 + (43783151027782973/289696986250000000000000000000 : ℝ)*base71 + (68557468001581/173130000000000000000000000 : ℝ)*base72 + (321546145744871/802170000000000000000000000 : ℝ)*base75 + (2136070346807/7213750000000000000000000 : ℝ)*base77 + (3056848566458846521/4629323070000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base81 + (5227/100000000000000000 : ℝ)*base86 + (5227/100000000000000000 : ℝ)*base88 + (5227/100000000000000000 : ℝ)*base90 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (174659/100000 : ℝ) (34911/20000 : ℝ) (15821/20000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]])
    (hprev0 : (0 : ℝ) ≤ ((17313/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(17313/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-80217/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-80217/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(40159/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(40159/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((11297/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(11297/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-51663/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-51663/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(43753/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(43753/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c315086_s1 p hpa hpb X hX hprev0

#print axioms solution
