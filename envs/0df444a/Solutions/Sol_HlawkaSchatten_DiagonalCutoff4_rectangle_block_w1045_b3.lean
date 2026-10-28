-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1045_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T13:50:31.155067+00:00
-- url     : https://prove2.me/submissions/abfd04e5-188b-4986-843e-0a060262dbe1

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
theorem support_rectangle_w1045_s9_0 (p : ℝ) (hpa : (8237/2048 : ℝ) ≤ p) (hpb : p ≤ (4119/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2214152421/10000000000 : ℝ)*x 0 + (5394698907/10000000000 : ℝ)*x 1 + (5264081953/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2214152421/10000000000 : ℝ)^4119 ≤ (2689028116679/20000000000000 : ℝ)^3095 := by
    have hnat : (2214152421 : ℕ)^4119*20000000000000^3095 ≤ 2689028116679^3095*10000000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2214152421 10000000000 2689028116679 20000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5394698907/10000000000 : ℝ)^4119 ≤ (2748950454147/6250000000000 : ℝ)^3095 := by
    have hnat : (5394698907 : ℕ)^4119*6250000000000^3095 ≤ 2748950454147^3095*10000000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394698907 10000000000 2748950454147 6250000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264081953/10000000000 : ℝ)^4119 ≤ (42571652128291/100000000000000 : ℝ)^3095 := by
    have hnat : (5264081953 : ℕ)^4119*100000000000000^3095 ≤ 42571652128291^3095*10000000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264081953 10000000000 42571652128291 100000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4119/1024 : ℝ)) 4119 3095 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2214152421/10000000000 : ℝ), (5394698907/10000000000 : ℝ), (5264081953/10000000000 : ℝ)] ![(2689028116679/20000000000000 : ℝ), (2748950454147/6250000000000 : ℝ), (42571652128291/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2214152421/10000000000 : ℝ)|^4119 ≤ (2689028116679/20000000000000 : ℝ)^3095
        have hw : |(-2214152421/10000000000 : ℝ)|=(2214152421/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5394698907/10000000000 : ℝ)|^4119 ≤ (2748950454147/6250000000000 : ℝ)^3095
        have hw : |(5394698907/10000000000 : ℝ)|=(5394698907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264081953/10000000000 : ℝ)|^4119 ≤ (42571652128291/100000000000000 : ℝ)^3095
        have hw : |(5264081953/10000000000 : ℝ)|=(5264081953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1045_s9_1 (p : ℝ) (hpa : (8237/2048 : ℝ) ≤ p) (hpb : p ≤ (4119/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (334063537/625000000 : ℝ)*x 0 + (-1140214471/5000000000 : ℝ)*x 1 + (5264083029/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (334063537/625000000 : ℝ)^4119 ≤ (43444950960653/100000000000000 : ℝ)^3095 := by
    have hnat : (334063537 : ℕ)^4119*100000000000000^3095 ≤ 43444950960653^3095*625000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334063537 625000000 43444950960653 100000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1140214471/5000000000 : ℝ)^4119 ≤ (2796677063087/20000000000000 : ℝ)^3095 := by
    have hnat : (1140214471 : ℕ)^4119*20000000000000^3095 ≤ 2796677063087^3095*5000000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1140214471 5000000000 2796677063087 20000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264083029/10000000000 : ℝ)^4119 ≤ (10642915927291/25000000000000 : ℝ)^3095 := by
    have hnat : (5264083029 : ℕ)^4119*25000000000000^3095 ≤ 10642915927291^3095*10000000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264083029 10000000000 10642915927291 25000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4119/1024 : ℝ)) 4119 3095 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(334063537/625000000 : ℝ), (-1140214471/5000000000 : ℝ), (5264083029/10000000000 : ℝ)] ![(43444950960653/100000000000000 : ℝ), (2796677063087/20000000000000 : ℝ), (10642915927291/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(334063537/625000000 : ℝ)|^4119 ≤ (43444950960653/100000000000000 : ℝ)^3095
        have hw : |(334063537/625000000 : ℝ)|=(334063537/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1140214471/5000000000 : ℝ)|^4119 ≤ (2796677063087/20000000000000 : ℝ)^3095
        have hw : |(-1140214471/5000000000 : ℝ)|=(1140214471/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264083029/10000000000 : ℝ)|^4119 ≤ (10642915927291/25000000000000 : ℝ)^3095
        have hw : |(5264083029/10000000000 : ℝ)|=(5264083029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1045_s9_2 (p : ℝ) (hpa : (8237/2048 : ℝ) ≤ p) (hpb : p ≤ (4119/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5345017199/10000000000 : ℝ)*x 0 + (5264082337/10000000000 : ℝ)*x 1 + (-45608581/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345017199/10000000000 : ℝ)^4119 ≤ (43444957526793/100000000000000 : ℝ)^3095 := by
    have hnat : (5345017199 : ℕ)^4119*100000000000000^3095 ≤ 43444957526793^3095*10000000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345017199 10000000000 43444957526793 100000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264082337/10000000000 : ℝ)^4119 ≤ (21285828130621/50000000000000 : ℝ)^3095 := by
    have hnat : (5264082337 : ℕ)^4119*50000000000000^3095 ≤ 21285828130621^3095*10000000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264082337 10000000000 21285828130621 50000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (45608581/200000000 : ℝ)^4119 ≤ (13983386196789/100000000000000 : ℝ)^3095 := by
    have hnat : (45608581 : ℕ)^4119*100000000000000^3095 ≤ 13983386196789^3095*200000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      45608581 200000000 13983386196789 100000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4119/1024 : ℝ)) 4119 3095 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345017199/10000000000 : ℝ), (5264082337/10000000000 : ℝ), (-45608581/200000000 : ℝ)] ![(43444957526793/100000000000000 : ℝ), (21285828130621/50000000000000 : ℝ), (13983386196789/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345017199/10000000000 : ℝ)|^4119 ≤ (43444957526793/100000000000000 : ℝ)^3095
        have hw : |(5345017199/10000000000 : ℝ)|=(5345017199/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264082337/10000000000 : ℝ)|^4119 ≤ (21285828130621/50000000000000 : ℝ)^3095
        have hw : |(5264082337/10000000000 : ℝ)|=(5264082337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-45608581/200000000 : ℝ)|^4119 ≤ (13983386196789/100000000000000 : ℝ)^3095
        have hw : |(-45608581/200000000 : ℝ)|=(45608581/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1045_s9_3 (p : ℝ) (hpa : (8237/2048 : ℝ) ≤ p) (hpb : p ≤ (4119/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4378522071/10000000000 : ℝ)*x 0 + (4252950087/10000000000 : ℝ)*x 1 + (4507872411/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4378522071/10000000000 : ℝ)^4119 ≤ (260284652143/781250000000 : ℝ)^3095 := by
    have hnat : (4378522071 : ℕ)^4119*781250000000^3095 ≤ 260284652143^3095*10000000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4378522071 10000000000 260284652143 781250000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4252950087/10000000000 : ℝ)^4119 ≤ (32050894707933/100000000000000 : ℝ)^3095 := by
    have hnat : (4252950087 : ℕ)^4119*100000000000000^3095 ≤ 32050894707933^3095*10000000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4252950087 10000000000 32050894707933 100000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4507872411/10000000000 : ℝ)^4119 ≤ (34632669802797/100000000000000 : ℝ)^3095 := by
    have hnat : (4507872411 : ℕ)^4119*100000000000000^3095 ≤ 34632669802797^3095*10000000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4507872411 10000000000 34632669802797 100000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4119/1024 : ℝ)) 4119 3095 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4378522071/10000000000 : ℝ), (4252950087/10000000000 : ℝ), (4507872411/10000000000 : ℝ)] ![(260284652143/781250000000 : ℝ), (32050894707933/100000000000000 : ℝ), (34632669802797/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4378522071/10000000000 : ℝ)|^4119 ≤ (260284652143/781250000000 : ℝ)^3095
        have hw : |(4378522071/10000000000 : ℝ)|=(4378522071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4252950087/10000000000 : ℝ)|^4119 ≤ (32050894707933/100000000000000 : ℝ)^3095
        have hw : |(4252950087/10000000000 : ℝ)|=(4252950087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4507872411/10000000000 : ℝ)|^4119 ≤ (34632669802797/100000000000000 : ℝ)^3095
        have hw : |(4507872411/10000000000 : ℝ)|=(4507872411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1045_s9_4 (p : ℝ) (hpa : (8237/2048 : ℝ) ≤ p) (hpb : p ≤ (4119/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2214157319/10000000000 : ℝ)*x 0 + (164512773/312500000 : ℝ)*x 1 + (5394371109/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2214157319/10000000000 : ℝ)^4119 ≤ (6722590083161/50000000000000 : ℝ)^3095 := by
    have hnat : (2214157319 : ℕ)^4119*50000000000000^3095 ≤ 6722590083161^3095*10000000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2214157319 10000000000 6722590083161 50000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (164512773/312500000 : ℝ)^4119 ≤ (425751692947/1000000000000 : ℝ)^3095 := by
    have hnat : (164512773 : ℕ)^4119*1000000000000^3095 ≤ 425751692947^3095*312500000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      164512773 312500000 425751692947 1000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5394371109/10000000000 : ℝ)^4119 ≤ (5497456315141/12500000000000 : ℝ)^3095 := by
    have hnat : (5394371109 : ℕ)^4119*12500000000000^3095 ≤ 5497456315141^3095*10000000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394371109 10000000000 5497456315141 12500000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4119/1024 : ℝ)) 4119 3095 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2214157319/10000000000 : ℝ), (164512773/312500000 : ℝ), (5394371109/10000000000 : ℝ)] ![(6722590083161/50000000000000 : ℝ), (425751692947/1000000000000 : ℝ), (5497456315141/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2214157319/10000000000 : ℝ)|^4119 ≤ (6722590083161/50000000000000 : ℝ)^3095
        have hw : |(-2214157319/10000000000 : ℝ)|=(2214157319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(164512773/312500000 : ℝ)|^4119 ≤ (425751692947/1000000000000 : ℝ)^3095
        have hw : |(164512773/312500000 : ℝ)|=(164512773/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5394371109/10000000000 : ℝ)|^4119 ≤ (5497456315141/12500000000000 : ℝ)^3095
        have hw : |(5394371109/10000000000 : ℝ)|=(5394371109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1045_s9_5 (p : ℝ) (hpa : (8237/2048 : ℝ) ≤ p) (hpb : p ≤ (4119/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1328043477/2500000000 : ℝ)*x 0 + (-537535023/2500000000 : ℝ)*x 1 + (43154961/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328043477/2500000000 : ℝ)^4119 ≤ (43090041357591/100000000000000 : ℝ)^3095 := by
    have hnat : (1328043477 : ℕ)^4119*100000000000000^3095 ≤ 43090041357591^3095*2500000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328043477 2500000000 43090041357591 100000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (537535023/2500000000 : ℝ)^4119 ≤ (6465159390143/50000000000000 : ℝ)^3095 := by
    have hnat : (537535023 : ℕ)^4119*50000000000000^3095 ≤ 6465159390143^3095*2500000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      537535023 2500000000 6465159390143 50000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (43154961/80000000 : ℝ)^4119 ≤ (1759185593777/4000000000000 : ℝ)^3095 := by
    have hnat : (43154961 : ℕ)^4119*4000000000000^3095 ≤ 1759185593777^3095*80000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      43154961 80000000 1759185593777 4000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4119/1024 : ℝ)) 4119 3095 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1328043477/2500000000 : ℝ), (-537535023/2500000000 : ℝ), (43154961/80000000 : ℝ)] ![(43090041357591/100000000000000 : ℝ), (6465159390143/50000000000000 : ℝ), (1759185593777/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1328043477/2500000000 : ℝ)|^4119 ≤ (43090041357591/100000000000000 : ℝ)^3095
        have hw : |(1328043477/2500000000 : ℝ)|=(1328043477/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-537535023/2500000000 : ℝ)|^4119 ≤ (6465159390143/50000000000000 : ℝ)^3095
        have hw : |(-537535023/2500000000 : ℝ)|=(537535023/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(43154961/80000000 : ℝ)|^4119 ≤ (1759185593777/4000000000000 : ℝ)^3095
        have hw : |(43154961/80000000 : ℝ)|=(43154961/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1045_s9_6 (p : ℝ) (hpa : (8237/2048 : ℝ) ≤ p) (hpb : p ≤ (4119/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2656086531/5000000000 : ℝ)*x 0 + (2697185431/5000000000 : ℝ)*x 1 + (-430028047/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656086531/5000000000 : ℝ)^4119 ≤ (8618006444949/20000000000000 : ℝ)^3095 := by
    have hnat : (2656086531 : ℕ)^4119*20000000000000^3095 ≤ 8618006444949^3095*5000000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656086531 5000000000 8618006444949 20000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2697185431/5000000000 : ℝ)^4119 ≤ (21989823920551/50000000000000 : ℝ)^3095 := by
    have hnat : (2697185431 : ℕ)^4119*50000000000000^3095 ≤ 21989823920551^3095*5000000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697185431 5000000000 21989823920551 50000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (430028047/2000000000 : ℝ)^4119 ≤ (1293031992477/10000000000000 : ℝ)^3095 := by
    have hnat : (430028047 : ℕ)^4119*10000000000000^3095 ≤ 1293031992477^3095*2000000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      430028047 2000000000 1293031992477 10000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4119/1024 : ℝ)) 4119 3095 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656086531/5000000000 : ℝ), (2697185431/5000000000 : ℝ), (-430028047/2000000000 : ℝ)] ![(8618006444949/20000000000000 : ℝ), (21989823920551/50000000000000 : ℝ), (1293031992477/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656086531/5000000000 : ℝ)|^4119 ≤ (8618006444949/20000000000000 : ℝ)^3095
        have hw : |(2656086531/5000000000 : ℝ)|=(2656086531/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2697185431/5000000000 : ℝ)|^4119 ≤ (21989823920551/50000000000000 : ℝ)^3095
        have hw : |(2697185431/5000000000 : ℝ)|=(2697185431/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-430028047/2000000000 : ℝ)|^4119 ≤ (1293031992477/10000000000000 : ℝ)^3095
        have hw : |(-430028047/2000000000 : ℝ)|=(430028047/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1045_s9_7 (p : ℝ) (hpa : (8237/2048 : ℝ) ≤ p) (hpb : p ≤ (4119/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4378532461/10000000000 : ℝ)*x 0 + (450723479/1000000000 : ℝ)*x 1 + (850717917/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4378532461/10000000000 : ℝ)^4119 ≤ (8329135172337/25000000000000 : ℝ)^3095 := by
    have hnat : (4378532461 : ℕ)^4119*25000000000000^3095 ≤ 8329135172337^3095*10000000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4378532461 10000000000 8329135172337 25000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (450723479/1000000000 : ℝ)^4119 ≤ (8656537637039/25000000000000 : ℝ)^3095 := by
    have hnat : (450723479 : ℕ)^4119*25000000000000^3095 ≤ 8656537637039^3095*1000000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      450723479 1000000000 8656537637039 25000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (850717917/2000000000 : ℝ)^4119 ≤ (1282292349527/4000000000000 : ℝ)^3095 := by
    have hnat : (850717917 : ℕ)^4119*4000000000000^3095 ≤ 1282292349527^3095*2000000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      850717917 2000000000 1282292349527 4000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4119/1024 : ℝ)) 4119 3095 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4378532461/10000000000 : ℝ), (450723479/1000000000 : ℝ), (850717917/2000000000 : ℝ)] ![(8329135172337/25000000000000 : ℝ), (8656537637039/25000000000000 : ℝ), (1282292349527/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4378532461/10000000000 : ℝ)|^4119 ≤ (8329135172337/25000000000000 : ℝ)^3095
        have hw : |(4378532461/10000000000 : ℝ)|=(4378532461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(450723479/1000000000 : ℝ)|^4119 ≤ (8656537637039/25000000000000 : ℝ)^3095
        have hw : |(450723479/1000000000 : ℝ)|=(450723479/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(850717917/2000000000 : ℝ)|^4119 ≤ (1282292349527/4000000000000 : ℝ)^3095
        have hw : |(850717917/2000000000 : ℝ)|=(850717917/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1045_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8237/2048 : ℝ) ≤ p) (hpb : p ≤ (4119/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73792343/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1399/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5611/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (11223/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (13989/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1399/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5611/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1399/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5611/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1399/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5611/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1399/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5611/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1399/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5611/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1399/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5611/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base29 : ((-1 : ℝ)*N 1+(-1 : ℝ)*N 2+(1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 0, f.sum]
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
  have hpowlo : (5611/50000 : ℝ) ^ (8237/2048 : ℝ) ≤ (7557507420355429/50000000000000000000 : ℝ) := by
    have hpowers : (5611/50000 : ℝ)^8237 ≤ (7557507420355429/50000000000000000000 : ℝ)^2048 := by
      have hnat : (5611 : ℕ)^8237*50000000000000000000^2048 ≤ 7557507420355429^2048*50000^8237 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5611 50000 7557507420355429 50000000000000000000 8237 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5611/50000 : ℝ)) (X := (7557507420355429/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8237 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (1399/10000 : ℝ) ^ (8237/2048 : ℝ) ≤ (36686155641825101/100000000000000000000 : ℝ) := by
    have hpowers : (1399/10000 : ℝ)^8237 ≤ (36686155641825101/100000000000000000000 : ℝ)^2048 := by
      have hnat : (1399 : ℕ)^8237*100000000000000000000^2048 ≤ 36686155641825101^2048*10000^8237 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1399 10000 36686155641825101 100000000000000000000 8237 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1399/10000 : ℝ)) (X := (36686155641825101/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8237 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (25007557507420355429/25000000000000000000 : ℝ) ≤ (1000075153661337/1000000000000000 : ℝ) ^ (8237/2048 : ℝ) := by
    have hpowers : (25007557507420355429/25000000000000000000 : ℝ)^2048 ≤ (1000075153661337/1000000000000000 : ℝ)^8237 := by
      have hnat : (25007557507420355429 : ℕ)^2048*1000000000000000^8237 ≤ 1000075153661337^8237*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25007557507420355429 25000000000000000000 1000075153661337 1000000000000000 2048 8237 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000075153661337/1000000000000000 : ℝ)) (X := (25007557507420355429/25000000000000000000 : ℝ)) (by norm_num) 8237 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100051801170482535959/100000000000000000000 : ℝ) ≤ (10001287703747073/10000000000000000 : ℝ) ^ (8237/2048 : ℝ) := by
    have hpowers : (100051801170482535959/100000000000000000000 : ℝ)^2048 ≤ (10001287703747073/10000000000000000 : ℝ)^8237 := by
      have hnat : (100051801170482535959 : ℕ)^2048*10000000000000000^8237 ≤ 10001287703747073^8237*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100051801170482535959 100000000000000000000 10001287703747073 10000000000000000 2048 8237 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001287703747073/10000000000000000 : ℝ)) (X := (100051801170482535959/100000000000000000000 : ℝ)) (by norm_num) 8237 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50036686155641825101/50000000000000000000 : ℝ) ≤ (1250227983860097/1250000000000000 : ℝ) ^ (8237/2048 : ℝ) := by
    have hpowers : (50036686155641825101/50000000000000000000 : ℝ)^2048 ≤ (1250227983860097/1250000000000000 : ℝ)^8237 := by
      have hnat : (50036686155641825101 : ℕ)^2048*1250000000000000^8237 ≤ 1250227983860097^8237*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50036686155641825101 50000000000000000000 1250227983860097 1250000000000000 2048 8237 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250227983860097/1250000000000000 : ℝ)) (X := (50036686155641825101/50000000000000000000 : ℝ)) (by norm_num) 8237 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(7557507420355429/50000000000000000000 : ℝ) ≤ ((6917511629549244507/6920000000000000000 : ℝ)+2*(536167133703/276800000000000 : ℝ)*(5611/50000 : ℝ))^(8237/2048 : ℝ) := by
    rw [show (6917511629549244507/6920000000000000000 : ℝ)+2*(536167133703/276800000000000 : ℝ)*(5611/50000 : ℝ)=(1000075153661337/1000000000000000 : ℝ) by norm_num, show 1+2*(7557507420355429/50000000000000000000 : ℝ)=(25007557507420355429/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(36686155641825101/100000000000000000000 : ℝ)+(7557507420355429/50000000000000000000 : ℝ) ≤ ((6917511629549244507/6920000000000000000 : ℝ)+(536167133703/276800000000000 : ℝ)*((1399/10000 : ℝ)+(5611/50000 : ℝ)))^(8237/2048 : ℝ) := by
    rw [show (6917511629549244507/6920000000000000000 : ℝ)+(536167133703/276800000000000 : ℝ)*((1399/10000 : ℝ)+(5611/50000 : ℝ))=(10001287703747073/10000000000000000 : ℝ) by norm_num, show 1+(36686155641825101/100000000000000000000 : ℝ)+(7557507420355429/50000000000000000000 : ℝ)=(100051801170482535959/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(36686155641825101/100000000000000000000 : ℝ) ≤ ((6917511629549244507/6920000000000000000 : ℝ)+2*(536167133703/276800000000000 : ℝ)*(1399/10000 : ℝ))^(8237/2048 : ℝ) := by
    rw [show (6917511629549244507/6920000000000000000 : ℝ)+2*(536167133703/276800000000000 : ℝ)*(1399/10000 : ℝ)=(1250227983860097/1250000000000000 : ℝ) by norm_num, show 1+2*(36686155641825101/100000000000000000000 : ℝ)=(50036686155641825101/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6917511629549244507/6920000000000000000 : ℝ)*(X 1 0+X 2 0)+(536167133703/276800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8237/2048 : ℝ)) (lo := (5611/50000 : ℝ)) (hi := (1399/10000 : ℝ)) (c := (6917511629549244507/6920000000000000000 : ℝ)) (alpha := (536167133703/276800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6917511629549244507/6920000000000000000 : ℝ)*(X 0 1+X 2 1)+(536167133703/276800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8237/2048 : ℝ)) (lo := (5611/50000 : ℝ)) (hi := (1399/10000 : ℝ)) (c := (6917511629549244507/6920000000000000000 : ℝ)) (alpha := (536167133703/276800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6917511629549244507/6920000000000000000 : ℝ)*(X 0 2+X 1 2)+(536167133703/276800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8237/2048 : ℝ)) (lo := (5611/50000 : ℝ)) (hi := (1399/10000 : ℝ)) (c := (6917511629549244507/6920000000000000000 : ℝ)) (alpha := (536167133703/276800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2214152421/10000000000 : ℝ)*X 0 0+(5394698907/10000000000 : ℝ)*X 0 1+(5264081953/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1045_s9_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((334063537/625000000 : ℝ)*X 1 0+(-1140214471/5000000000 : ℝ)*X 1 1+(5264083029/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1045_s9_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5345017199/10000000000 : ℝ)*X 2 0+(5264082337/10000000000 : ℝ)*X 2 1+(-45608581/200000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1045_s9_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4378522071/10000000000 : ℝ)*X 0 0+(4252950087/10000000000 : ℝ)*X 0 1+(4507872411/10000000000 : ℝ)*X 0 2+(4378522071/10000000000 : ℝ)*X 1 0+(4252950087/10000000000 : ℝ)*X 1 1+(4507872411/10000000000 : ℝ)*X 1 2+(4378522071/10000000000 : ℝ)*X 2 0+(4252950087/10000000000 : ℝ)*X 2 1+(4507872411/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1045_s9_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2214157319/10000000000 : ℝ)*X 0 0+(164512773/312500000 : ℝ)*X 0 1+(5394371109/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1045_s9_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1328043477/2500000000 : ℝ)*X 1 0+(-537535023/2500000000 : ℝ)*X 1 1+(43154961/80000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1045_s9_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2656086531/5000000000 : ℝ)*X 2 0+(2697185431/5000000000 : ℝ)*X 2 1+(-430028047/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1045_s9_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4378532461/10000000000 : ℝ)*X 0 0+(450723479/1000000000 : ℝ)*X 0 1+(850717917/2000000000 : ℝ)*X 0 2+(4378532461/10000000000 : ℝ)*X 1 0+(450723479/1000000000 : ℝ)*X 1 1+(850717917/2000000000 : ℝ)*X 1 2+(4378532461/10000000000 : ℝ)*X 2 0+(450723479/1000000000 : ℝ)*X 2 1+(850717917/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1045_s9_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (56548612592737979457092979/69200000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (393738757/100000000000000 : ℝ)*(base21) + (379591461/50000000000000 : ℝ)*(base29) + (246551839/100000000000000 : ℝ)*(lower2) + (1964199/20000000000000 : ℝ)*(upper3) + (319634113/100000000000000 : ℝ)*(upper4) + (5789377734572217/100000000000000 : ℝ)*(major0) + (5789378493755139/100000000000000 : ℝ)*(major1) + (5789378493755139/100000000000000 : ℝ)*(major2) + (95699686192543/1250000000000 : ℝ)*(sp0) + (7656006049520819/100000000000000 : ℝ)*(sp1) + (239249398271599/3125000000000 : ℝ)*(sp2) + (392275015156731/10000000000000 : ℝ)*(sp3) + (319133003/1000000000000 : ℝ)*(sp4) + (24911090893/100000000000000 : ℝ)*(sp6) + (392275015156731/10000000000000 : ℝ)*(f.failure) + (7656006808703739/100000000000000 : ℝ)*(f.sum) + (29439578619083/13840000000000000000000000000 : ℝ)*base66 + (13510061576558303527/692000000000000000000000000000000 : ℝ)*base68 + (4109600433918303527/692000000000000000000000000000000 : ℝ)*base70 + (1084274981811012981/692000000000000000000000000000000 : ℝ)*base72 + (3237875813577/6920000000000000000000000000 : ℝ)*base73 + (10706889013274453527/692000000000000000000000000000000 : ℝ)*base76 + (5601023995211012981/692000000000000000000000000000000 : ℝ)*base78 + (7829241745446453527/692000000000000000000000000000000 : ℝ)*base80 + (12122875032783/6920000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/50000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (2289267/500000000000000000000 : ℝ)*base90 + (2289267/500000000000000000000 : ℝ)*base92 + (2289267/500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (347887821285487302040644069/86500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (140176841/12500000000000 : ℝ)*(base19) + (412338329/100000000000000 : ℝ)*(base23) + (10261711/12500000000000 : ℝ)*(upper3) + (138832921/50000000000000 : ℝ)*(lower4) + (25742991/50000000000000 : ℝ)*(upper5) + (2909267761589289/50000000000000 : ℝ)*(major0) + (2909267761589289/50000000000000 : ℝ)*(major1) + (2909267761589289/50000000000000 : ℝ)*(major2) + (25801296961/100000000000000 : ℝ)*(sp0) + (1028973031/100000000000000 : ℝ)*(sp1) + (307781552987637/4000000000000 : ℝ)*(sp4) + (7694562475600127/100000000000000 : ℝ)*(sp5) + (1923641053412389/25000000000000 : ℝ)*(sp6) + (985626571577111/25000000000000 : ℝ)*(sp7) + (985626571577111/25000000000000 : ℝ)*(f.failure) + (3847282312993943/50000000000000 : ℝ)*(f.sum) + (40163896246593/6920000000000000000000000000 : ℝ)*base66 + (3786392002449539477/346000000000000000000000000000000 : ℝ)*base68 + (3760122717455539477/346000000000000000000000000000000 : ℝ)*base70 + (5137248027539539477/346000000000000000000000000000000 : ℝ)*base72 + (8677229539087/6920000000000000000000000000 : ℝ)*base73 + (3155475993591539477/346000000000000000000000000000000 : ℝ)*base76 + (4924473183723539477/346000000000000000000000000000000 : ℝ)*base78 + (1470526181180460523/346000000000000000000000000000000 : ℝ)*base79 + (24094217246433/6920000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (861073/1250000000000000000000 : ℝ)*base89 + (861073/1250000000000000000000 : ℝ)*base91 + (861073/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1045_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8237/2048 : ℝ) ≤ p) (hpb : p ≤ (4119/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73792343/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1399/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5611/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11223/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (13989/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1045_s9 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1045_box_0 (p : ℝ) (hpa : (8237/2048 : ℝ) ≤ p) (hpb : p ≤ (4119/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1041982427/5000000000 : ℝ)*x 0 + (5377648281/10000000000 : ℝ)*x 1 + (5377648291/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1041982427/5000000000 : ℝ)^4119 ≤ (62017041423/500000000000 : ℝ)^3095 := by
    have hnat : (1041982427 : ℕ)^4119*500000000000^3095 ≤ 62017041423^3095*5000000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1041982427 5000000000 62017041423 500000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5377648281/10000000000 : ℝ)^4119 ≤ (4379829579339/10000000000000 : ℝ)^3095 := by
    have hnat : (5377648281 : ℕ)^4119*10000000000000^3095 ≤ 4379829579339^3095*10000000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5377648281 10000000000 4379829579339 10000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5377648291/10000000000 : ℝ)^4119 ≤ (21899147950891/50000000000000 : ℝ)^3095 := by
    have hnat : (5377648291 : ℕ)^4119*50000000000000^3095 ≤ 21899147950891^3095*10000000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5377648291 10000000000 21899147950891 50000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4119/1024 : ℝ)) 4119 3095 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1041982427/5000000000 : ℝ), (5377648281/10000000000 : ℝ), (5377648291/10000000000 : ℝ)] ![(62017041423/500000000000 : ℝ), (4379829579339/10000000000000 : ℝ), (21899147950891/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1041982427/5000000000 : ℝ)|^4119 ≤ (62017041423/500000000000 : ℝ)^3095
        have hw : |(-1041982427/5000000000 : ℝ)|=(1041982427/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5377648281/10000000000 : ℝ)|^4119 ≤ (4379829579339/10000000000000 : ℝ)^3095
        have hw : |(5377648281/10000000000 : ℝ)|=(5377648281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5377648291/10000000000 : ℝ)|^4119 ≤ (21899147950891/50000000000000 : ℝ)^3095
        have hw : |(5377648291/10000000000 : ℝ)|=(5377648291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1045_box_1 (p : ℝ) (hpa : (8237/2048 : ℝ) ≤ p) (hpb : p ≤ (4119/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5294961721/10000000000 : ℝ)*x 0 + (-2195842763/10000000000 : ℝ)*x 1 + (537764823/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5294961721/10000000000 : ℝ)^4119 ≤ (10726082463771/25000000000000 : ℝ)^3095 := by
    have hnat : (5294961721 : ℕ)^4119*25000000000000^3095 ≤ 10726082463771^3095*10000000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5294961721 10000000000 10726082463771 25000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2195842763/10000000000 : ℝ)^4119 ≤ (1329737489981/10000000000000 : ℝ)^3095 := by
    have hnat : (2195842763 : ℕ)^4119*10000000000000^3095 ≤ 1329737489981^3095*10000000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2195842763 10000000000 1329737489981 10000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (537764823/1000000000 : ℝ)^4119 ≤ (2737393452537/6250000000000 : ℝ)^3095 := by
    have hnat : (537764823 : ℕ)^4119*6250000000000^3095 ≤ 2737393452537^3095*1000000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      537764823 1000000000 2737393452537 6250000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4119/1024 : ℝ)) 4119 3095 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5294961721/10000000000 : ℝ), (-2195842763/10000000000 : ℝ), (537764823/1000000000 : ℝ)] ![(10726082463771/25000000000000 : ℝ), (1329737489981/10000000000000 : ℝ), (2737393452537/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5294961721/10000000000 : ℝ)|^4119 ≤ (10726082463771/25000000000000 : ℝ)^3095
        have hw : |(5294961721/10000000000 : ℝ)|=(5294961721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2195842763/10000000000 : ℝ)|^4119 ≤ (1329737489981/10000000000000 : ℝ)^3095
        have hw : |(-2195842763/10000000000 : ℝ)|=(2195842763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(537764823/1000000000 : ℝ)|^4119 ≤ (2737393452537/6250000000000 : ℝ)^3095
        have hw : |(537764823/1000000000 : ℝ)|=(537764823/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1045_box_2 (p : ℝ) (hpa : (8237/2048 : ℝ) ≤ p) (hpb : p ≤ (4119/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (330935097/625000000 : ℝ)*x 0 + (672206051/1250000000 : ℝ)*x 1 + (-548960687/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (330935097/625000000 : ℝ)^4119 ≤ (5363041004079/12500000000000 : ℝ)^3095 := by
    have hnat : (330935097 : ℕ)^4119*12500000000000^3095 ≤ 5363041004079^3095*625000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      330935097 625000000 5363041004079 12500000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (672206051/1250000000 : ℝ)^4119 ≤ (10949574292491/25000000000000 : ℝ)^3095 := by
    have hnat : (672206051 : ℕ)^4119*25000000000000^3095 ≤ 10949574292491^3095*1250000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      672206051 1250000000 10949574292491 25000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (548960687/2500000000 : ℝ)^4119 ≤ (13297374778921/100000000000000 : ℝ)^3095 := by
    have hnat : (548960687 : ℕ)^4119*100000000000000^3095 ≤ 13297374778921^3095*2500000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      548960687 2500000000 13297374778921 100000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4119/1024 : ℝ)) 4119 3095 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(330935097/625000000 : ℝ), (672206051/1250000000 : ℝ), (-548960687/2500000000 : ℝ)] ![(5363041004079/12500000000000 : ℝ), (10949574292491/25000000000000 : ℝ), (13297374778921/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(330935097/625000000 : ℝ)|^4119 ≤ (5363041004079/12500000000000 : ℝ)^3095
        have hw : |(330935097/625000000 : ℝ)|=(330935097/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(672206051/1250000000 : ℝ)|^4119 ≤ (10949574292491/25000000000000 : ℝ)^3095
        have hw : |(672206051/1250000000 : ℝ)|=(672206051/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-548960687/2500000000 : ℝ)|^4119 ≤ (13297374778921/100000000000000 : ℝ)^3095
        have hw : |(-548960687/2500000000 : ℝ)|=(548960687/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1045_box_3 (p : ℝ) (hpa : (8237/2048 : ℝ) ≤ p) (hpb : p ≤ (4119/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (448714847/1000000000 : ℝ)*x 0 + (4326387239/10000000000 : ℝ)*x 1 + (2163193599/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (448714847/1000000000 : ℝ)^4119 ≤ (1721046875799/5000000000000 : ℝ)^3095 := by
    have hnat : (448714847 : ℕ)^4119*5000000000000^3095 ≤ 1721046875799^3095*1000000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      448714847 1000000000 1721046875799 5000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4326387239/10000000000 : ℝ)^4119 ≤ (32789531440299/100000000000000 : ℝ)^3095 := by
    have hnat : (4326387239 : ℕ)^4119*100000000000000^3095 ≤ 32789531440299^3095*10000000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4326387239 10000000000 32789531440299 100000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2163193599/5000000000 : ℝ)^4119 ≤ (512336422293/1562500000000 : ℝ)^3095 := by
    have hnat : (2163193599 : ℕ)^4119*1562500000000^3095 ≤ 512336422293^3095*5000000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2163193599 5000000000 512336422293 1562500000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4119/1024 : ℝ)) 4119 3095 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(448714847/1000000000 : ℝ), (4326387239/10000000000 : ℝ), (2163193599/5000000000 : ℝ)] ![(1721046875799/5000000000000 : ℝ), (32789531440299/100000000000000 : ℝ), (512336422293/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(448714847/1000000000 : ℝ)|^4119 ≤ (1721046875799/5000000000000 : ℝ)^3095
        have hw : |(448714847/1000000000 : ℝ)|=(448714847/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4326387239/10000000000 : ℝ)|^4119 ≤ (32789531440299/100000000000000 : ℝ)^3095
        have hw : |(4326387239/10000000000 : ℝ)|=(4326387239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2163193599/5000000000 : ℝ)|^4119 ≤ (512336422293/1562500000000 : ℝ)^3095
        have hw : |(2163193599/5000000000 : ℝ)|=(2163193599/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1045_box_4 (p : ℝ) (hpa : (8237/2048 : ℝ) ≤ p) (hpb : p ≤ (4119/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1172863617/5000000000 : ℝ)*x 0 + (5279772971/10000000000 : ℝ)*x 1 + (5279772513/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1172863617/5000000000 : ℝ)^4119 ≤ (226855824173/1562500000000 : ℝ)^3095 := by
    have hnat : (1172863617 : ℕ)^4119*1562500000000^3095 ≤ 226855824173^3095*5000000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1172863617 5000000000 226855824173 1562500000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5279772971/10000000000 : ℝ)^4119 ≤ (42740616088113/100000000000000 : ℝ)^3095 := by
    have hnat : (5279772971 : ℕ)^4119*100000000000000^3095 ≤ 42740616088113^3095*10000000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5279772971 10000000000 42740616088113 100000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5279772513/10000000000 : ℝ)^4119 ≤ (10685152788463/25000000000000 : ℝ)^3095 := by
    have hnat : (5279772513 : ℕ)^4119*25000000000000^3095 ≤ 10685152788463^3095*10000000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5279772513 10000000000 10685152788463 25000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4119/1024 : ℝ)) 4119 3095 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1172863617/5000000000 : ℝ), (5279772971/10000000000 : ℝ), (5279772513/10000000000 : ℝ)] ![(226855824173/1562500000000 : ℝ), (42740616088113/100000000000000 : ℝ), (10685152788463/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1172863617/5000000000 : ℝ)|^4119 ≤ (226855824173/1562500000000 : ℝ)^3095
        have hw : |(-1172863617/5000000000 : ℝ)|=(1172863617/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5279772971/10000000000 : ℝ)|^4119 ≤ (42740616088113/100000000000000 : ℝ)^3095
        have hw : |(5279772971/10000000000 : ℝ)|=(5279772971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5279772513/10000000000 : ℝ)|^4119 ≤ (10685152788463/25000000000000 : ℝ)^3095
        have hw : |(5279772513/10000000000 : ℝ)|=(5279772513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1045_box_5 (p : ℝ) (hpa : (8237/2048 : ℝ) ≤ p) (hpb : p ≤ (4119/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1341065923/2500000000 : ℝ)*x 0 + (-1117020779/5000000000 : ℝ)*x 1 + (5279772437/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1341065923/2500000000 : ℝ)^4119 ≤ (43653277748987/100000000000000 : ℝ)^3095 := by
    have hnat : (1341065923 : ℕ)^4119*100000000000000^3095 ≤ 43653277748987^3095*2500000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1341065923 2500000000 43653277748987 100000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1117020779/5000000000 : ℝ)^4119 ≤ (680305595181/5000000000000 : ℝ)^3095 := by
    have hnat : (1117020779 : ℕ)^4119*5000000000000^3095 ≤ 680305595181^3095*5000000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1117020779 5000000000 680305595181 5000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5279772437/10000000000 : ℝ)^4119 ≤ (21370305167533/50000000000000 : ℝ)^3095 := by
    have hnat : (5279772437 : ℕ)^4119*50000000000000^3095 ≤ 21370305167533^3095*10000000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5279772437 10000000000 21370305167533 50000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4119/1024 : ℝ)) 4119 3095 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1341065923/2500000000 : ℝ), (-1117020779/5000000000 : ℝ), (5279772437/10000000000 : ℝ)] ![(43653277748987/100000000000000 : ℝ), (680305595181/5000000000000 : ℝ), (21370305167533/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1341065923/2500000000 : ℝ)|^4119 ≤ (43653277748987/100000000000000 : ℝ)^3095
        have hw : |(1341065923/2500000000 : ℝ)|=(1341065923/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1117020779/5000000000 : ℝ)|^4119 ≤ (680305595181/5000000000000 : ℝ)^3095
        have hw : |(-1117020779/5000000000 : ℝ)|=(1117020779/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5279772437/10000000000 : ℝ)|^4119 ≤ (21370305167533/50000000000000 : ℝ)^3095
        have hw : |(5279772437/10000000000 : ℝ)|=(5279772437/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1045_box_6 (p : ℝ) (hpa : (8237/2048 : ℝ) ≤ p) (hpb : p ≤ (4119/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1341065693/2500000000 : ℝ)*x 0 + (1055954641/2000000000 : ℝ)*x 1 + (-2234041767/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1341065693/2500000000 : ℝ)^4119 ≤ (43653267785171/100000000000000 : ℝ)^3095 := by
    have hnat : (1341065693 : ℕ)^4119*100000000000000^3095 ≤ 43653267785171^3095*2500000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1341065693 2500000000 43653267785171 100000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1055954641/2000000000 : ℝ)^4119 ≤ (5342577326139/12500000000000 : ℝ)^3095 := by
    have hnat : (1055954641 : ℕ)^4119*12500000000000^3095 ≤ 5342577326139^3095*2000000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1055954641 2000000000 5342577326139 12500000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2234041767/10000000000 : ℝ)^4119 ≤ (13606113597647/100000000000000 : ℝ)^3095 := by
    have hnat : (2234041767 : ℕ)^4119*100000000000000^3095 ≤ 13606113597647^3095*10000000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2234041767 10000000000 13606113597647 100000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4119/1024 : ℝ)) 4119 3095 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1341065693/2500000000 : ℝ), (1055954641/2000000000 : ℝ), (-2234041767/10000000000 : ℝ)] ![(43653267785171/100000000000000 : ℝ), (5342577326139/12500000000000 : ℝ), (13606113597647/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1341065693/2500000000 : ℝ)|^4119 ≤ (43653267785171/100000000000000 : ℝ)^3095
        have hw : |(1341065693/2500000000 : ℝ)|=(1341065693/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1055954641/2000000000 : ℝ)|^4119 ≤ (5342577326139/12500000000000 : ℝ)^3095
        have hw : |(1055954641/2000000000 : ℝ)|=(1055954641/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2234041767/10000000000 : ℝ)|^4119 ≤ (13606113597647/100000000000000 : ℝ)^3095
        have hw : |(-2234041767/10000000000 : ℝ)|=(2234041767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1045_box_7 (p : ℝ) (hpa : (8237/2048 : ℝ) ≤ p) (hpb : p ≤ (4119/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4269576047/10000000000 : ℝ)*x 0 + (2217576053/5000000000 : ℝ)*x 1 + (4435151473/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4269576047/10000000000 : ℝ)^4119 ≤ (2013609573849/6250000000000 : ℝ)^3095 := by
    have hnat : (4269576047 : ℕ)^4119*6250000000000^3095 ≤ 2013609573849^3095*10000000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4269576047 10000000000 2013609573849 6250000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2217576053/5000000000 : ℝ)^4119 ≤ (33891126625611/100000000000000 : ℝ)^3095 := by
    have hnat : (2217576053 : ℕ)^4119*100000000000000^3095 ≤ 33891126625611^3095*5000000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2217576053 5000000000 33891126625611 100000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4435151473/10000000000 : ℝ)^4119 ≤ (4236390023523/12500000000000 : ℝ)^3095 := by
    have hnat : (4435151473 : ℕ)^4119*12500000000000^3095 ≤ 4236390023523^3095*10000000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4435151473 10000000000 4236390023523 12500000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4119/1024 : ℝ)) 4119 3095 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4269576047/10000000000 : ℝ), (2217576053/5000000000 : ℝ), (4435151473/10000000000 : ℝ)] ![(2013609573849/6250000000000 : ℝ), (33891126625611/100000000000000 : ℝ), (4236390023523/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4269576047/10000000000 : ℝ)|^4119 ≤ (2013609573849/6250000000000 : ℝ)^3095
        have hw : |(4269576047/10000000000 : ℝ)|=(4269576047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2217576053/5000000000 : ℝ)|^4119 ≤ (33891126625611/100000000000000 : ℝ)^3095
        have hw : |(2217576053/5000000000 : ℝ)|=(2217576053/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4435151473/10000000000 : ℝ)|^4119 ≤ (4236390023523/12500000000000 : ℝ)^3095
        have hw : |(4435151473/10000000000 : ℝ)|=(4435151473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1045_box_8 (p : ℝ) (hpa : (8237/2048 : ℝ) ≤ p) (hpb : p ≤ (4119/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-572777247/2500000000 : ℝ)*x 0 + (5213399831/10000000000 : ℝ)*x 1 + (2693622829/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (572777247/2500000000 : ℝ)^4119 ≤ (7035304661297/50000000000000 : ℝ)^3095 := by
    have hnat : (572777247 : ℕ)^4119*50000000000000^3095 ≤ 7035304661297^3095*2500000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      572777247 2500000000 7035304661297 50000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5213399831/10000000000 : ℝ)^4119 ≤ (42027036583173/100000000000000 : ℝ)^3095 := by
    have hnat : (5213399831 : ℕ)^4119*100000000000000^3095 ≤ 42027036583173^3095*10000000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5213399831 10000000000 42027036583173 100000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2693622829/5000000000 : ℝ)^4119 ≤ (5487794259711/12500000000000 : ℝ)^3095 := by
    have hnat : (2693622829 : ℕ)^4119*12500000000000^3095 ≤ 5487794259711^3095*5000000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2693622829 5000000000 5487794259711 12500000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4119/1024 : ℝ)) 4119 3095 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-572777247/2500000000 : ℝ), (5213399831/10000000000 : ℝ), (2693622829/5000000000 : ℝ)] ![(7035304661297/50000000000000 : ℝ), (42027036583173/100000000000000 : ℝ), (5487794259711/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-572777247/2500000000 : ℝ)|^4119 ≤ (7035304661297/50000000000000 : ℝ)^3095
        have hw : |(-572777247/2500000000 : ℝ)|=(572777247/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5213399831/10000000000 : ℝ)|^4119 ≤ (42027036583173/100000000000000 : ℝ)^3095
        have hw : |(5213399831/10000000000 : ℝ)|=(5213399831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2693622829/5000000000 : ℝ)|^4119 ≤ (5487794259711/12500000000000 : ℝ)^3095
        have hw : |(2693622829/5000000000 : ℝ)|=(2693622829/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1045_box_9 (p : ℝ) (hpa : (8237/2048 : ℝ) ≤ p) (hpb : p ≤ (4119/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2644081133/5000000000 : ℝ)*x 0 + (-219202629/1000000000 : ℝ)*x 1 + (5387245499/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2644081133/5000000000 : ℝ)^4119 ≤ (42831021876189/100000000000000 : ℝ)^3095 := by
    have hnat : (2644081133 : ℕ)^4119*100000000000000^3095 ≤ 42831021876189^3095*5000000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2644081133 5000000000 42831021876189 100000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (219202629/1000000000 : ℝ)^4119 ≤ (6633312876423/50000000000000 : ℝ)^3095 := by
    have hnat : (219202629 : ℕ)^4119*50000000000000^3095 ≤ 6633312876423^3095*1000000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      219202629 1000000000 6633312876423 50000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5387245499/10000000000 : ℝ)^4119 ≤ (43902352353243/100000000000000 : ℝ)^3095 := by
    have hnat : (5387245499 : ℕ)^4119*100000000000000^3095 ≤ 43902352353243^3095*10000000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5387245499 10000000000 43902352353243 100000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4119/1024 : ℝ)) 4119 3095 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2644081133/5000000000 : ℝ), (-219202629/1000000000 : ℝ), (5387245499/10000000000 : ℝ)] ![(42831021876189/100000000000000 : ℝ), (6633312876423/50000000000000 : ℝ), (43902352353243/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2644081133/5000000000 : ℝ)|^4119 ≤ (42831021876189/100000000000000 : ℝ)^3095
        have hw : |(2644081133/5000000000 : ℝ)|=(2644081133/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-219202629/1000000000 : ℝ)|^4119 ≤ (6633312876423/50000000000000 : ℝ)^3095
        have hw : |(-219202629/1000000000 : ℝ)|=(219202629/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5387245499/10000000000 : ℝ)|^4119 ≤ (43902352353243/100000000000000 : ℝ)^3095
        have hw : |(5387245499/10000000000 : ℝ)|=(5387245499/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1045_box_10 (p : ℝ) (hpa : (8237/2048 : ℝ) ≤ p) (hpb : p ≤ (4119/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5288162543/10000000000 : ℝ)*x 0 + (5387245619/10000000000 : ℝ)*x 1 + (-1096012879/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5288162543/10000000000 : ℝ)^4119 ≤ (8566204972403/20000000000000 : ℝ)^3095 := by
    have hnat : (5288162543 : ℕ)^4119*20000000000000^3095 ≤ 8566204972403^3095*10000000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5288162543 10000000000 8566204972403 20000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5387245619/10000000000 : ℝ)^4119 ≤ (43902353654711/100000000000000 : ℝ)^3095 := by
    have hnat : (5387245619 : ℕ)^4119*100000000000000^3095 ≤ 43902353654711^3095*10000000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5387245619 10000000000 43902353654711 100000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1096012879/5000000000 : ℝ)^4119 ≤ (663331073389/5000000000000 : ℝ)^3095 := by
    have hnat : (1096012879 : ℕ)^4119*5000000000000^3095 ≤ 663331073389^3095*5000000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1096012879 5000000000 663331073389 5000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4119/1024 : ℝ)) 4119 3095 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5288162543/10000000000 : ℝ), (5387245619/10000000000 : ℝ), (-1096012879/5000000000 : ℝ)] ![(8566204972403/20000000000000 : ℝ), (43902353654711/100000000000000 : ℝ), (663331073389/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5288162543/10000000000 : ℝ)|^4119 ≤ (8566204972403/20000000000000 : ℝ)^3095
        have hw : |(5288162543/10000000000 : ℝ)|=(5288162543/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5387245619/10000000000 : ℝ)|^4119 ≤ (43902353654711/100000000000000 : ℝ)^3095
        have hw : |(5387245619/10000000000 : ℝ)|=(5387245619/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1096012879/5000000000 : ℝ)|^4119 ≤ (663331073389/5000000000000 : ℝ)^3095
        have hw : |(-1096012879/5000000000 : ℝ)|=(1096012879/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1045_box_11 (p : ℝ) (hpa : (8237/2048 : ℝ) ≤ p) (hpb : p ≤ (4119/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4508209163/10000000000 : ℝ)*x 0 + (4315716253/10000000000 : ℝ)*x 1 + (4315716477/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4508209163/10000000000 : ℝ)^4119 ≤ (17318056496627/50000000000000 : ℝ)^3095 := by
    have hnat : (4508209163 : ℕ)^4119*50000000000000^3095 ≤ 17318056496627^3095*10000000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4508209163 10000000000 17318056496627 50000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4315716253/10000000000 : ℝ)^4119 ≤ (1021310698921/3125000000000 : ℝ)^3095 := by
    have hnat : (4315716253 : ℕ)^4119*3125000000000^3095 ≤ 1021310698921^3095*10000000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4315716253 10000000000 1021310698921 3125000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4315716477/10000000000 : ℝ)^4119 ≤ (6536388924601/20000000000000 : ℝ)^3095 := by
    have hnat : (4315716477 : ℕ)^4119*20000000000000^3095 ≤ 6536388924601^3095*10000000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4315716477 10000000000 6536388924601 20000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4119/1024 : ℝ)) 4119 3095 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4508209163/10000000000 : ℝ), (4315716253/10000000000 : ℝ), (4315716477/10000000000 : ℝ)] ![(17318056496627/50000000000000 : ℝ), (1021310698921/3125000000000 : ℝ), (6536388924601/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4508209163/10000000000 : ℝ)|^4119 ≤ (17318056496627/50000000000000 : ℝ)^3095
        have hw : |(4508209163/10000000000 : ℝ)|=(4508209163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4315716253/10000000000 : ℝ)|^4119 ≤ (1021310698921/3125000000000 : ℝ)^3095
        have hw : |(4315716253/10000000000 : ℝ)|=(4315716253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4315716477/10000000000 : ℝ)|^4119 ≤ (6536388924601/20000000000000 : ℝ)^3095
        have hw : |(4315716477/10000000000 : ℝ)|=(4315716477/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1045_box_12 (p : ℝ) (hpa : (8237/2048 : ℝ) ≤ p) (hpb : p ≤ (4119/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2138965991/10000000000 : ℝ)*x 0 + (1088533791/2000000000 : ℝ)*x 1 + (5271783503/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2138965991/10000000000 : ℝ)^4119 ≤ (1605120642739/12500000000000 : ℝ)^3095 := by
    have hnat : (2138965991 : ℕ)^4119*12500000000000^3095 ≤ 1605120642739^3095*10000000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2138965991 10000000000 1605120642739 12500000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1088533791/2000000000 : ℝ)^4119 ≤ (11126117924743/25000000000000 : ℝ)^3095 := by
    have hnat : (1088533791 : ℕ)^4119*25000000000000^3095 ≤ 11126117924743^3095*2000000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1088533791 2000000000 11126117924743 25000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5271783503/10000000000 : ℝ)^4119 ≤ (5331820392269/12500000000000 : ℝ)^3095 := by
    have hnat : (5271783503 : ℕ)^4119*12500000000000^3095 ≤ 5331820392269^3095*10000000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5271783503 10000000000 5331820392269 12500000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4119/1024 : ℝ)) 4119 3095 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2138965991/10000000000 : ℝ), (1088533791/2000000000 : ℝ), (5271783503/10000000000 : ℝ)] ![(1605120642739/12500000000000 : ℝ), (11126117924743/25000000000000 : ℝ), (5331820392269/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2138965991/10000000000 : ℝ)|^4119 ≤ (1605120642739/12500000000000 : ℝ)^3095
        have hw : |(-2138965991/10000000000 : ℝ)|=(2138965991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1088533791/2000000000 : ℝ)|^4119 ≤ (11126117924743/25000000000000 : ℝ)^3095
        have hw : |(1088533791/2000000000 : ℝ)|=(1088533791/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5271783503/10000000000 : ℝ)|^4119 ≤ (5331820392269/12500000000000 : ℝ)^3095
        have hw : |(5271783503/10000000000 : ℝ)|=(5271783503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1045_box_13 (p : ℝ) (hpa : (8237/2048 : ℝ) ≤ p) (hpb : p ≤ (4119/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (671239761/1250000000 : ℝ)*x 0 + (-139818777/625000000 : ℝ)*x 1 + (263589171/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (671239761/1250000000 : ℝ)^4119 ≤ (43714526862229/100000000000000 : ℝ)^3095 := by
    have hnat : (671239761 : ℕ)^4119*100000000000000^3095 ≤ 43714526862229^3095*1250000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      671239761 1250000000 43714526862229 100000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (139818777/625000000 : ℝ)^4119 ≤ (2726182177047/20000000000000 : ℝ)^3095 := by
    have hnat : (139818777 : ℕ)^4119*20000000000000^3095 ≤ 2726182177047^3095*625000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      139818777 625000000 2726182177047 20000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (263589171/500000000 : ℝ)^4119 ≤ (106636405611/250000000000 : ℝ)^3095 := by
    have hnat : (263589171 : ℕ)^4119*250000000000^3095 ≤ 106636405611^3095*500000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263589171 500000000 106636405611 250000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4119/1024 : ℝ)) 4119 3095 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(671239761/1250000000 : ℝ), (-139818777/625000000 : ℝ), (263589171/500000000 : ℝ)] ![(43714526862229/100000000000000 : ℝ), (2726182177047/20000000000000 : ℝ), (106636405611/250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(671239761/1250000000 : ℝ)|^4119 ≤ (43714526862229/100000000000000 : ℝ)^3095
        have hw : |(671239761/1250000000 : ℝ)|=(671239761/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-139818777/625000000 : ℝ)|^4119 ≤ (2726182177047/20000000000000 : ℝ)^3095
        have hw : |(-139818777/625000000 : ℝ)|=(139818777/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(263589171/500000000 : ℝ)|^4119 ≤ (106636405611/250000000000 : ℝ)^3095
        have hw : |(263589171/500000000 : ℝ)|=(263589171/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1045_box_14 (p : ℝ) (hpa : (8237/2048 : ℝ) ≤ p) (hpb : p ≤ (4119/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (671239759/1250000000 : ℝ)*x 0 + (658972927/1250000000 : ℝ)*x 1 + (-2237100457/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (671239759/1250000000 : ℝ)^4119 ≤ (8742905337777/20000000000000 : ℝ)^3095 := by
    have hnat : (671239759 : ℕ)^4119*20000000000000^3095 ≤ 8742905337777^3095*1250000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      671239759 1250000000 8742905337777 20000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (658972927/1250000000 : ℝ)^4119 ≤ (2665910137583/6250000000000 : ℝ)^3095 := by
    have hnat : (658972927 : ℕ)^4119*6250000000000^3095 ≤ 2665910137583^3095*1250000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658972927 1250000000 2665910137583 6250000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2237100457/10000000000 : ℝ)^4119 ≤ (13630911087961/100000000000000 : ℝ)^3095 := by
    have hnat : (2237100457 : ℕ)^4119*100000000000000^3095 ≤ 13630911087961^3095*10000000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2237100457 10000000000 13630911087961 100000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4119/1024 : ℝ)) 4119 3095 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(671239759/1250000000 : ℝ), (658972927/1250000000 : ℝ), (-2237100457/10000000000 : ℝ)] ![(8742905337777/20000000000000 : ℝ), (2665910137583/6250000000000 : ℝ), (13630911087961/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(671239759/1250000000 : ℝ)|^4119 ≤ (8742905337777/20000000000000 : ℝ)^3095
        have hw : |(671239759/1250000000 : ℝ)|=(671239759/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(658972927/1250000000 : ℝ)|^4119 ≤ (2665910137583/6250000000000 : ℝ)^3095
        have hw : |(658972927/1250000000 : ℝ)|=(658972927/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2237100457/10000000000 : ℝ)|^4119 ≤ (13630911087961/100000000000000 : ℝ)^3095
        have hw : |(-2237100457/10000000000 : ℝ)|=(2237100457/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1045_box_15 (p : ℝ) (hpa : (8237/2048 : ℝ) ≤ p) (hpb : p ≤ (4119/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1062896847/2500000000 : ℝ)*x 0 + (2222012237/5000000000 : ℝ)*x 1 + (2222012237/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062896847/2500000000 : ℝ)^4119 ≤ (6407445637687/20000000000000 : ℝ)^3095 := by
    have hnat : (1062896847 : ℕ)^4119*20000000000000^3095 ≤ 6407445637687^3095*2500000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062896847 2500000000 6407445637687 20000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2222012237/5000000000 : ℝ)^4119 ≤ (33981385893663/100000000000000 : ℝ)^3095 := by
    have hnat : (2222012237 : ℕ)^4119*100000000000000^3095 ≤ 33981385893663^3095*5000000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2222012237 5000000000 33981385893663 100000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2222012237/5000000000 : ℝ)^4119 ≤ (33981385893663/100000000000000 : ℝ)^3095 := by
    have hnat : (2222012237 : ℕ)^4119*100000000000000^3095 ≤ 33981385893663^3095*5000000000^4119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2222012237 5000000000 33981385893663 100000000000000 4119 3095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4119/1024 : ℝ)) 4119 3095 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062896847/2500000000 : ℝ), (2222012237/5000000000 : ℝ), (2222012237/5000000000 : ℝ)] ![(6407445637687/20000000000000 : ℝ), (33981385893663/100000000000000 : ℝ), (33981385893663/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062896847/2500000000 : ℝ)|^4119 ≤ (6407445637687/20000000000000 : ℝ)^3095
        have hw : |(1062896847/2500000000 : ℝ)|=(1062896847/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2222012237/5000000000 : ℝ)|^4119 ≤ (33981385893663/100000000000000 : ℝ)^3095
        have hw : |(2222012237/5000000000 : ℝ)|=(2222012237/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2222012237/5000000000 : ℝ)|^4119 ≤ (33981385893663/100000000000000 : ℝ)^3095
        have hw : |(2222012237/5000000000 : ℝ)|=(2222012237/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1045_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8237/2048 : ℝ) ≤ p) (hpb : p ≤ (4119/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73792343/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13989/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11223/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(3889/6250 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(2369/4000 : ℝ) ∧ (39753/50000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (10363/12500 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (13989/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11223/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (13989/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11223/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (13989/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11223/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (13989/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11223/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (13989/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11223/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (13989/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11223/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11223/100000 : ℝ) ^ (8237/2048 : ℝ) ≤ (15120432802058489/100000000000000000000 : ℝ) := by
    have hpowers : (11223/100000 : ℝ)^8237 ≤ (15120432802058489/100000000000000000000 : ℝ)^2048 := by
      have hnat : (11223 : ℕ)^8237*100000000000000000000^2048 ≤ 15120432802058489^2048*100000^8237 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11223 100000 15120432802058489 100000000000000000000 8237 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11223/100000 : ℝ)) (X := (15120432802058489/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8237 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (13989/100000 : ℝ) ^ (8237/2048 : ℝ) ≤ (36675609910628151/100000000000000000000 : ℝ) := by
    have hpowers : (13989/100000 : ℝ)^8237 ≤ (36675609910628151/100000000000000000000 : ℝ)^2048 := by
      have hnat : (13989 : ℕ)^8237*100000000000000000000^2048 ≤ 36675609910628151^2048*100000^8237 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13989 100000 36675609910628151 100000000000000000000 8237 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (13989/100000 : ℝ)) (X := (36675609910628151/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8237 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50015120432802058489/50000000000000000000 : ℝ) ≤ (10000751805970289/10000000000000000 : ℝ) ^ (8237/2048 : ℝ) := by
    have hpowers : (50015120432802058489/50000000000000000000 : ℝ)^2048 ≤ (10000751805970289/10000000000000000 : ℝ)^8237 := by
      have hnat : (50015120432802058489 : ℕ)^2048*10000000000000000^8237 ≤ 10000751805970289^8237*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50015120432802058489 50000000000000000000 10000751805970289 10000000000000000 2048 8237 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000751805970289/10000000000000000 : ℝ)) (X := (50015120432802058489/50000000000000000000 : ℝ)) (by norm_num) 8237 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (1250647450533908583/1250000000000000000 : ℝ) ≤ (10001287576302769/10000000000000000 : ℝ) ^ (8237/2048 : ℝ) := by
    have hpowers : (1250647450533908583/1250000000000000000 : ℝ)^2048 ≤ (10001287576302769/10000000000000000 : ℝ)^8237 := by
      have hnat : (1250647450533908583 : ℕ)^2048*10000000000000000^8237 ≤ 10001287576302769^8237*1250000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1250647450533908583 1250000000000000000 10001287576302769 10000000000000000 2048 8237 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001287576302769/10000000000000000 : ℝ)) (X := (1250647450533908583/1250000000000000000 : ℝ)) (by norm_num) 8237 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50036675609910628151/50000000000000000000 : ℝ) ≤ (10001823346635249/10000000000000000 : ℝ) ^ (8237/2048 : ℝ) := by
    have hpowers : (50036675609910628151/50000000000000000000 : ℝ)^2048 ≤ (10001823346635249/10000000000000000 : ℝ)^8237 := by
      have hnat : (50036675609910628151 : ℕ)^2048*10000000000000000^8237 ≤ 10001823346635249^8237*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50036675609910628151 50000000000000000000 10001823346635249 10000000000000000 2048 8237 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001823346635249/10000000000000000 : ℝ)) (X := (50036675609910628151/50000000000000000000 : ℝ)) (by norm_num) 8237 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(15120432802058489/100000000000000000000 : ℝ) ≤ ((4608342265738495549/4610000000000000000 : ℝ)+2*(1674282289/864375000000 : ℝ)*(11223/100000 : ℝ))^(8237/2048 : ℝ) := by
    rw [show (4608342265738495549/4610000000000000000 : ℝ)+2*(1674282289/864375000000 : ℝ)*(11223/100000 : ℝ)=(10000751805970289/10000000000000000 : ℝ) by norm_num, show 1+2*(15120432802058489/100000000000000000000 : ℝ)=(50015120432802058489/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(36675609910628151/100000000000000000000 : ℝ)+(15120432802058489/100000000000000000000 : ℝ) ≤ ((4608342265738495549/4610000000000000000 : ℝ)+(1674282289/864375000000 : ℝ)*((13989/100000 : ℝ)+(11223/100000 : ℝ)))^(8237/2048 : ℝ) := by
    rw [show (4608342265738495549/4610000000000000000 : ℝ)+(1674282289/864375000000 : ℝ)*((13989/100000 : ℝ)+(11223/100000 : ℝ))=(10001287576302769/10000000000000000 : ℝ) by norm_num, show 1+(36675609910628151/100000000000000000000 : ℝ)+(15120432802058489/100000000000000000000 : ℝ)=(1250647450533908583/1250000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(36675609910628151/100000000000000000000 : ℝ) ≤ ((4608342265738495549/4610000000000000000 : ℝ)+2*(1674282289/864375000000 : ℝ)*(13989/100000 : ℝ))^(8237/2048 : ℝ) := by
    rw [show (4608342265738495549/4610000000000000000 : ℝ)+2*(1674282289/864375000000 : ℝ)*(13989/100000 : ℝ)=(10001823346635249/10000000000000000 : ℝ) by norm_num, show 1+2*(36675609910628151/100000000000000000000 : ℝ)=(50036675609910628151/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4608342265738495549/4610000000000000000 : ℝ)*(X 1 0+X 2 0)+(1674282289/864375000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8237/2048 : ℝ)) (lo := (11223/100000 : ℝ)) (hi := (13989/100000 : ℝ)) (c := (4608342265738495549/4610000000000000000 : ℝ)) (alpha := (1674282289/864375000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4608342265738495549/4610000000000000000 : ℝ)*(X 0 1+X 2 1)+(1674282289/864375000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8237/2048 : ℝ)) (lo := (11223/100000 : ℝ)) (hi := (13989/100000 : ℝ)) (c := (4608342265738495549/4610000000000000000 : ℝ)) (alpha := (1674282289/864375000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4608342265738495549/4610000000000000000 : ℝ)*(X 0 2+X 1 2)+(1674282289/864375000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8237/2048 : ℝ)) (lo := (11223/100000 : ℝ)) (hi := (13989/100000 : ℝ)) (c := (4608342265738495549/4610000000000000000 : ℝ)) (alpha := (1674282289/864375000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1041982427/5000000000 : ℝ)*X 0 0+(5377648281/10000000000 : ℝ)*X 0 1+(5377648291/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1045_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5294961721/10000000000 : ℝ)*X 1 0+(-2195842763/10000000000 : ℝ)*X 1 1+(537764823/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1045_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((330935097/625000000 : ℝ)*X 2 0+(672206051/1250000000 : ℝ)*X 2 1+(-548960687/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1045_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((448714847/1000000000 : ℝ)*X 0 0+(4326387239/10000000000 : ℝ)*X 0 1+(2163193599/5000000000 : ℝ)*X 0 2+(448714847/1000000000 : ℝ)*X 1 0+(4326387239/10000000000 : ℝ)*X 1 1+(2163193599/5000000000 : ℝ)*X 1 2+(448714847/1000000000 : ℝ)*X 2 0+(4326387239/10000000000 : ℝ)*X 2 1+(2163193599/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1045_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1172863617/5000000000 : ℝ)*X 0 0+(5279772971/10000000000 : ℝ)*X 0 1+(5279772513/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1045_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1341065923/2500000000 : ℝ)*X 1 0+(-1117020779/5000000000 : ℝ)*X 1 1+(5279772437/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1045_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1341065693/2500000000 : ℝ)*X 2 0+(1055954641/2000000000 : ℝ)*X 2 1+(-2234041767/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1045_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4269576047/10000000000 : ℝ)*X 0 0+(2217576053/5000000000 : ℝ)*X 0 1+(4435151473/10000000000 : ℝ)*X 0 2+(4269576047/10000000000 : ℝ)*X 1 0+(2217576053/5000000000 : ℝ)*X 1 1+(4435151473/10000000000 : ℝ)*X 1 2+(4269576047/10000000000 : ℝ)*X 2 0+(2217576053/5000000000 : ℝ)*X 2 1+(4435151473/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1045_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-572777247/2500000000 : ℝ)*X 0 0+(5213399831/10000000000 : ℝ)*X 0 1+(2693622829/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1045_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((2644081133/5000000000 : ℝ)*X 1 0+(-219202629/1000000000 : ℝ)*X 1 1+(5387245499/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1045_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5288162543/10000000000 : ℝ)*X 2 0+(5387245619/10000000000 : ℝ)*X 2 1+(-1096012879/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1045_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4508209163/10000000000 : ℝ)*X 0 0+(4315716253/10000000000 : ℝ)*X 0 1+(4315716477/10000000000 : ℝ)*X 0 2+(4508209163/10000000000 : ℝ)*X 1 0+(4315716253/10000000000 : ℝ)*X 1 1+(4315716477/10000000000 : ℝ)*X 1 2+(4508209163/10000000000 : ℝ)*X 2 0+(4315716253/10000000000 : ℝ)*X 2 1+(4315716477/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1045_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-2138965991/10000000000 : ℝ)*X 0 0+(1088533791/2000000000 : ℝ)*X 0 1+(5271783503/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1045_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((671239761/1250000000 : ℝ)*X 1 0+(-139818777/625000000 : ℝ)*X 1 1+(263589171/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1045_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((671239759/1250000000 : ℝ)*X 2 0+(658972927/1250000000 : ℝ)*X 2 1+(-2237100457/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1045_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((1062896847/2500000000 : ℝ)*X 0 0+(2222012237/5000000000 : ℝ)*X 0 1+(2222012237/5000000000 : ℝ)*X 0 2+(1062896847/2500000000 : ℝ)*X 1 0+(2222012237/5000000000 : ℝ)*X 1 1+(2222012237/5000000000 : ℝ)*X 1 2+(1062896847/2500000000 : ℝ)*X 2 0+(2222012237/5000000000 : ℝ)*X 2 1+(2222012237/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1045_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-3889/6250 : ℝ) ≤ (-35854874236333541249411151/57625000000000000000000000 : ℝ) := by norm_num
    linear_combination (56265681/100000000000000 : ℝ)*(upper0) + (152045587/100000000000000 : ℝ)*(upper1) + (12159181/6250000000000 : ℝ)*(upper2) + (162692199/50000000000000 : ℝ)*(upper3) + (1919477124073399/50000000000000 : ℝ)*(major0) + (1919477124073399/50000000000000 : ℝ)*(major1) + (1919477124073399/50000000000000 : ℝ)*(major2) + (2708528729/12500000000000 : ℝ)*(sp1) + (2769423833/12500000000000 : ℝ)*(sp3) + (127436536215627/2500000000000 : ℝ)*(sp4) + (318589986274703/6250000000000 : ℝ)*(sp5) + (5097241735341299/100000000000000 : ℝ)*(sp6) + (650291309726921/25000000000000 : ℝ)*(sp7) + (109856641891/50000000000000 : ℝ)*(sp14) + (650296848574587/25000000000000 : ℝ)*(f.failure) + (127436536215627/2500000000000 : ℝ)*(f.sum) + (160675263133/69150000000000000000000000 : ℝ)*base66 + (7178902022688403153/691500000000000000000000000000000 : ℝ)*base67 + (6033403268717596847/691500000000000000000000000000000 : ℝ)*base70 + (3687038735094403153/691500000000000000000000000000000 : ℝ)*base71 + (755528101387/172875000000000000000000000 : ℝ)*base74 + (4386077875001596847/691500000000000000000000000000000 : ℝ)*base76 + (2414587011768403153/691500000000000000000000000000000 : ℝ)*base77 + (4122102636832096847/691500000000000000000000000000000 : ℝ)*base80 + (1988048032847/1383000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (9987341/1250000000000000000000 : ℝ)*base89 + (9987341/1250000000000000000000 : ℝ)*base91 + (9987341/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (2369/4000 : ℝ) ≤ (34129985219222616565053102012597/57625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (29546059/100000000000000 : ℝ)*(upper1) + (2461587/2000000000000 : ℝ)*(upper2) + (1830909/4000000000000 : ℝ)*(upper3) + (41933957/50000000000000 : ℝ)*(upper4) + (45585309/100000000000000 : ℝ)*(upper5) + (1950745474891149/50000000000000 : ℝ)*(major0) + (1950745474891149/50000000000000 : ℝ)*(major1) + (1950745474891149/50000000000000 : ℝ)*(major2) + (80307476403199/1562500000000 : ℝ)*(sp0) + (321226807159107/6250000000000 : ℝ)*(sp1) + (160614889943797/3125000000000 : ℝ)*(sp2) + (165222551858391/6250000000000 : ℝ)*(sp3) + (2011603233/100000000000000 : ℝ)*(sp6) + (3098453689/6250000000000 : ℝ)*(sp9) + (165222551858391/6250000000000 : ℝ)*(f.failure) + (80307476403199/1562500000000 : ℝ)*(f.sum) + (71532643399/14406250000000000000000000 : ℝ)*base66 + (4745554277787995801/230500000000000000000000000000000 : ℝ)*base67 + (3606482547635995801/230500000000000000000000000000000 : ℝ)*base69 + (3675746370379995801/230500000000000000000000000000000 : ℝ)*base71 + (1207490833/2881250000000000000000000 : ℝ)*base74 + (7623458219444004199/230500000000000000000000000000000 : ℝ)*base76 + (3314359861665995801/230500000000000000000000000000000 : ℝ)*base77 + (2717726244867495801/230500000000000000000000000000000 : ℝ)*base79 + (11018028514117/461000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (5149887/312500000000000000000 : ℝ)*base90 + (5149887/312500000000000000000 : ℝ)*base92 + (5149887/312500000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (39753/50000 : ℝ) ≤ (91633454016631590971189037263353/115250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (161119819/100000000000000 : ℝ)*(upper0) + (122957359/100000000000000 : ℝ)*(lower3) + (316538359/100000000000000 : ℝ)*(upper4) + (2184906270585789/50000000000000 : ℝ)*(major0) + (2184906270585789/50000000000000 : ℝ)*(major1) + (218490627058579/5000000000000 : ℝ)*(major2) + (23738734521/20000000000000 : ℝ)*(sp1) + (87478413941/25000000000000 : ℝ)*(sp2) + (29247345521/25000000000000 : ℝ)*(sp3) + (7668588069/100000000000000 : ℝ)*(sp4) + (5752229802849753/100000000000000 : ℝ)*(sp8) + (5752118777765217/100000000000000 : ℝ)*(sp9) + (2875943778891029/50000000000000 : ℝ)*(sp10) + (2960767814866223/100000000000000 : ℝ)*(sp11) + (2960884804248307/100000000000000 : ℝ)*(f.failure) + (2876118735718911/50000000000000 : ℝ)*(f.sum) + (338682199757/276600000000000000000000000 : ℝ)*base66 + (3715177556028040517/691500000000000000000000000000000 : ℝ)*base68 + (345131547319264871/23050000000000000000000000000000 : ℝ)*base69 + (3822045090916540517/691500000000000000000000000000000 : ℝ)*base72 + (18569698794871/691500000000000000000000000 : ℝ)*base73 + (231306554515164871/23050000000000000000000000000000 : ℝ)*base75 + (980571015844346839/230500000000000000000000000000000 : ℝ)*base78 + (5666743788786653161/230500000000000000000000000000000 : ℝ)*base79 + (2854515160061/461000000000000000000000000 : ℝ)*base81 + (27313301/5000000000000000000000 : ℝ)*base89 + (27313301/5000000000000000000000 : ℝ)*base91 + (72686699/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-10363/12500 : ℝ) ≤ (-23886081771960679096598532598821/28812500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (827877/4000000000000 : ℝ)*(lower0) + (11356603/100000000000000 : ℝ)*(lower1) + (2394547/12500000000000 : ℝ)*(lower4) + (1101055047746543/25000000000000 : ℝ)*(major0) + (1101055047746543/25000000000000 : ℝ)*(major1) + (1101055047746543/25000000000000 : ℝ)*(major2) + (2332700969/100000000000000 : ℝ)*(sp0) + (105923244539/100000000000000 : ℝ)*(sp5) + (61611737653/50000000000000 : ℝ)*(sp6) + (2272151381/50000000000000 : ℝ)*(sp7) + (2925936672175989/50000000000000 : ℝ)*(sp12) + (5851769753808407/100000000000000 : ℝ)*(sp13) + (146293811339441/2500000000000 : ℝ)*(sp14) + (2984194094698423/100000000000000 : ℝ)*(sp15) + (93256207468787/3125000000000 : ℝ)*(f.failure) + (2925937838526473/50000000000000 : ℝ)*(f.sum) + (1277335015153/691500000000000000000000000 : ℝ)*base66 + (1972955542089161321/345750000000000000000000000000000 : ℝ)*base67 + (848550225236838679/345750000000000000000000000000000 : ℝ)*base70 + (2174829912242411321/345750000000000000000000000000000 : ℝ)*base71 + (942389165519/172875000000000000000000000 : ℝ)*base73 + (2159657825185661321/345750000000000000000000000000000 : ℝ)*base75 + (2348578101101411321/345750000000000000000000000000000 : ℝ)*base77 + (30070306233675911321/345750000000000000000000000000000 : ℝ)*base79 + (659363879969/691500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1652059/156250000000000000000 : ℝ)*base90 + (1652059/156250000000000000000 : ℝ)*base92 + (1652059/156250000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1045_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8237/2048 : ℝ) ≤ p) (hpb : p ≤ (4119/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73792343/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13989/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11223/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(3889/6250 : ℝ) ≤ X j i ∧ X j i ≤ -(2369/4000 : ℝ) else (39753/50000 : ℝ) ≤ X j i ∧ X j i ≤ (10363/12500 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1045_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1045_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8237/2048 : ℝ) ≤ p) (hpb : p ≤ (4119/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73792343/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1399/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5611/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(3889/6250 : ℝ) ≤ X j i ∧ X j i ≤ -(2369/4000 : ℝ) else (39753/50000 : ℝ) ≤ X j i ∧ X j i ≤ (10363/12500 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1045_s9 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1045_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8237/2048 : ℝ) ≤ p) (hpb : p ≤ (4119/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73792343/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1399/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5611/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(3889/6250 : ℝ) ≤ X j i ∧ X j i ≤ -(2369/4000 : ℝ) else (39753/50000 : ℝ) ≤ X j i ∧ X j i ≤ (10363/12500 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1045_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
