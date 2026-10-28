-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff6.sign_e004_c05_s0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-27T19:24:58.187088+00:00
-- url     : https://prove2.me/submissions/7d05b96a-8a26-4787-bd35-68410ddf2cbf

import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Definitions.Def_HlawkaSchatten_GapComparison
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Basic
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Normalization
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Tactic.Ring
import Mathlib.Analysis.MeanInequalities
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FinCases
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
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
set_option exponentiation.threshold 20000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff6
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle
theorem support_e004_c05_s0_0 (p : ℝ) (hpa : (13/2 : ℝ) ≤ p) (hpb : p ≤ (53/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-50191541/5000000000 : ℝ)*x 0 + (55305887/100000000 : ℝ)*x 1 + (5530588593/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (53/8 : ℝ)) 53 45 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(-50191541/5000000000 : ℝ), (55305887/100000000 : ℝ), (5530588593/10000000000 : ℝ)] ![(442996376987/100000000000000 : ℝ), (49778502367357/100000000000000 : ℝ), (12444625308271/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_e004_c05_s0_1 (p : ℝ) (hpa : (13/2 : ℝ) ≤ p) (hpb : p ≤ (53/8 : ℝ)) (x : Fin 3 → ℝ) :
    (684882307/1000000000 : ℝ)*x 0 + (-466008421/2000000000 : ℝ)*x 1 + (2330042133/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (53/8 : ℝ)) 53 45 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(684882307/1000000000 : ℝ), (-466008421/2000000000 : ℝ), (2330042133/10000000000 : ℝ)] ![(32015634967851/50000000000000 : ℝ), (17984364899043/100000000000000 : ℝ), (17984365153581/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_e004_c05_s0_2 (p : ℝ) (hpa : (13/2 : ℝ) ≤ p) (hpb : p ≤ (53/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2698462237/5000000000 : ℝ)*x 0 + (3167265437/10000000000 : ℝ)*x 1 + (-791816369/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (53/8 : ℝ)) 53 45 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(2698462237/5000000000 : ℝ), (3167265437/10000000000 : ℝ), (-791816369/2500000000 : ℝ)] ![(3022789670397/6250000000000 : ℝ), (5163536488787/20000000000000 : ℝ), (25817682818357/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_e004_c05_s0_7 (p : ℝ) (hpa : (13/2 : ℝ) ≤ p) (hpb : p ≤ (53/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-39108231/5000000000 : ℝ)*x 0 + (1383977143/2500000000 : ℝ)*x 1 + (2767954279/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (53/8 : ℝ)) 53 45 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(-39108231/5000000000 : ℝ), (1383977143/2500000000 : ℝ), (2767954279/5000000000 : ℝ)] ![(16509860417/5000000000000 : ℝ), (24917450730511/50000000000000 : ℝ), (49834901312587/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_e004_c05_s0_9 (p : ℝ) (hpa : (13/2 : ℝ) ≤ p) (hpb : p ≤ (53/8 : ℝ)) (x : Fin 3 → ℝ) :
    (661041437/1250000000 : ℝ)*x 0 + (334671323/1250000000 : ℝ)*x 1 + (-3759897457/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (53/8 : ℝ)) 53 45 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(661041437/1250000000 : ℝ), (334671323/1250000000 : ℝ), (-3759897457/10000000000 : ℝ)] ![(11805133090263/25000000000000 : ℝ), (21182039530809/100000000000000 : ℝ), (31597428087091/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_e004_c05_s0_15 (p : ℝ) (hpa : (13/2 : ℝ) ≤ p) (hpb : p ≤ (53/8 : ℝ)) (x : Fin 3 → ℝ) :
    (6818584823/10000000000 : ℝ)*x 0 + (-344882543/1250000000 : ℝ)*x 1 + (1924337049/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (53/8 : ℝ)) 53 45 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(6818584823/10000000000 : ℝ), (-344882543/1250000000 : ℝ), (1924337049/10000000000 : ℝ)] ![(63698437645131/100000000000000 : ℝ), (21945271989951/100000000000000 : ℝ), (2871258069811/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_e004_c05_s0_16 (p : ℝ) (hpa : (13/2 : ℝ) ≤ p) (hpb : p ≤ (53/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1315455683/2500000000 : ℝ)*x 0 + (1409527991/5000000000 : ℝ)*x 1 + (-3653778563/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (53/8 : ℝ)) 53 45 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(1315455683/2500000000 : ℝ), (1409527991/5000000000 : ℝ), (-3653778563/10000000000 : ℝ)] ![(293386715929/625000000000 : ℝ), (4501677240099/20000000000000 : ℝ), (30549739236903/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_e004_c05_s0_17 (p : ℝ) (hpa : (13/2 : ℝ) ≤ p) (hpb : p ≤ (53/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1999999997/2000000000 : ℝ)*x 0 + (0 : ℝ)*x 1 + (-367/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (53/8 : ℝ)) 53 45 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(1999999997/2000000000 : ℝ), (0 : ℝ), (-367/10000000000 : ℝ)] ![(49999999911667/50000000000000 : ℝ), (0 : ℝ), (43729/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_e004_c05_s0_21 (p : ℝ) (hpa : (13/2 : ℝ) ≤ p) (hpb : p ≤ (53/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-367131539/10000000000 : ℝ)*x 0 + (2673642887/5000000000 : ℝ)*x 1 + (27813287/50000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (53/8 : ℝ)) 53 45 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(-367131539/10000000000 : ℝ), (2673642887/5000000000 : ℝ), (27813287/50000000 : ℝ)] ![(2040228852783/100000000000000 : ℝ), (23920571863841/50000000000000 : ℝ), (50118627406581/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_e004_c05_s0_23 (p : ℝ) (hpa : (13/2 : ℝ) ≤ p) (hpb : p ≤ (53/8 : ℝ)) (x : Fin 3 → ℝ) :
    (27457393/78125000 : ℝ)*x 0 + (2019170171/5000000000 : ℝ)*x 1 + (-2122172291/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (53/8 : ℝ)) 53 45 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(27457393/78125000 : ℝ), (2019170171/5000000000 : ℝ), (-2122172291/5000000000 : ℝ)] ![(14591667396211/50000000000000 : ℝ), (34371188315227/100000000000000 : ℝ), (36445476876843/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_e004_c05_s0_27 (p : ℝ) (hpa : (13/2 : ℝ) ≤ p) (hpb : p ≤ (53/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-104894877/10000000000 : ℝ)*x 0 + (808771193/2000000000 : ℝ)*x 1 + (6946390817/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (53/8 : ℝ)) 53 45 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(-104894877/10000000000 : ℝ), (808771193/2000000000 : ℝ), (6946390817/10000000000 : ℝ)] ![(58317431099/12500000000000 : ℝ), (34426485403343/100000000000000 : ℝ), (32553487571157/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_e004_c05_s0_28 (p : ℝ) (hpa : (13/2 : ℝ) ≤ p) (hpb : p ≤ (53/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1617170577/2000000000 : ℝ)*x 0 + (-377045669/2000000000 : ℝ)*x 1 + (1186856823/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (53/8 : ℝ)) 53 45 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(1617170577/2000000000 : ℝ), (-377045669/2000000000 : ℝ), (1186856823/10000000000 : ℝ)] ![(77861280093679/100000000000000 : ℝ), (11210623391/80000000000 : ℝ), (406272032947/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_e004_c05_s0_29 (p : ℝ) (hpa : (13/2 : ℝ) ≤ p) (hpb : p ≤ (53/8 : ℝ)) (x : Fin 3 → ℝ) :
    (320608039/500000000 : ℝ)*x 0 + (1560483879/5000000000 : ℝ)*x 1 + (-2039720097/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (53/8 : ℝ)) 53 45 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(320608039/500000000 : ℝ), (1560483879/5000000000 : ℝ), (-2039720097/10000000000 : ℝ)] ![(29625390218199/50000000000000 : ℝ), (25373779089149/100000000000000 : ℝ), (1921930058337/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_e004_c05_s0_32 (p : ℝ) (hpa : (13/2 : ℝ) ≤ p) (hpb : p ≤ (53/8 : ℝ)) (x : Fin 3 → ℝ) :
    (113662697/5000000000 : ℝ)*x 0 + (496822337/1250000000 : ℝ)*x 1 + (6946390817/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (53/8 : ℝ)) 53 45 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(113662697/5000000000 : ℝ), (496822337/1250000000 : ℝ), (6946390817/10000000000 : ℝ)] ![(1160102806319/100000000000000 : ℝ), (1349316881693/4000000000000 : ℝ), (32553487571157/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_e004_c05_s0_33 (p : ℝ) (hpa : (13/2 : ℝ) ≤ p) (hpb : p ≤ (53/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-154709819/10000000000 : ℝ)*x 0 + (5636416707/10000000000 : ℝ)*x 1 + (5396526387/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (53/8 : ℝ)) 53 45 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(-154709819/10000000000 : ℝ), (5636416707/10000000000 : ℝ), (5396526387/10000000000 : ℝ)] ![(737317241627/100000000000000 : ℝ), (12725562418587/25000000000000 : ℝ), (4836043307439/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_e004_c05_s0_34 (p : ℝ) (hpa : (13/2 : ℝ) ≤ p) (hpb : p ≤ (53/8 : ℝ)) (x : Fin 3 → ℝ) :
    (8498058603/10000000000 : ℝ)*x 0 + (-10413211/80000000 : ℝ)*x 1 + (304714821/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (53/8 : ℝ)) 53 45 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(8498058603/10000000000 : ℝ), (-10413211/80000000 : ℝ), (304714821/2500000000 : ℝ)] ![(16511416573161/20000000000000 : ℝ), (2264704392421/25000000000000 : ℝ), (4192049776671/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_e004_c05_s0_35 (p : ℝ) (hpa : (13/2 : ℝ) ≤ p) (hpb : p ≤ (53/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3532837489/10000000000 : ℝ)*x 0 + (2116429441/5000000000 : ℝ)*x 1 + (-806414243/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (53/8 : ℝ)) 53 45 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(3532837489/10000000000 : ℝ), (2116429441/5000000000 : ℝ), (-806414243/2000000000 : ℝ)] ![(14681150580339/50000000000000 : ℝ), (1816467279089/5000000000000 : ℝ), (34308353246423/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_e004_c05_s0_38 (p : ℝ) (hpa : (13/2 : ℝ) ≤ p) (hpb : p ≤ (53/8 : ℝ)) (x : Fin 3 → ℝ) :
    (232124837/2000000000 : ℝ)*x 0 + (1052869577/2000000000 : ℝ)*x 1 + (5087651507/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (53/8 : ℝ)) 53 45 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(232124837/2000000000 : ℝ), (1052869577/2000000000 : ℝ), (5087651507/10000000000 : ℝ)] ![(3957168783369/50000000000000 : ℝ), (146776275009/312500000000 : ℝ), (2255862720937/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_e004_c05_s0_39 (p : ℝ) (hpa : (13/2 : ℝ) ≤ p) (hpb : p ≤ (53/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-125811339/10000000000 : ℝ)*x 0 + (3479729519/5000000000 : ℝ)*x 1 + (200917003/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (53/8 : ℝ)) 53 45 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(-125811339/10000000000 : ℝ), (3479729519/5000000000 : ℝ), (200917003/500000000 : ℝ)] ![(577952558573/100000000000000 : ℝ), (32625629992927/50000000000000 : ℝ), (34170787440641/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_e004_c05_s0_40 (p : ℝ) (hpa : (13/2 : ℝ) ≤ p) (hpb : p ≤ (53/8 : ℝ)) (x : Fin 3 → ℝ) :
    (8079628369/10000000000 : ℝ)*x 0 + (-606014373/5000000000 : ℝ)*x 1 + (1870052947/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (53/8 : ℝ)) 53 45 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(8079628369/10000000000 : ℝ), (-606014373/5000000000 : ℝ), (1870052947/10000000000 : ℝ)] ![(77790691436097/100000000000000 : ℝ), (4164394729511/50000000000000 : ℝ), (111044152761/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_e004_c05_s0_41 (p : ℝ) (hpa : (13/2 : ℝ) ≤ p) (hpb : p ≤ (53/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3209778683/5000000000 : ℝ)*x 0 + (251199209/1250000000 : ℝ)*x 1 + (-3140445027/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (53/8 : ℝ)) 53 45 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(3209778683/5000000000 : ℝ), (251199209/1250000000 : ℝ), (-3140445027/10000000000 : ℝ)] ![(29665643274183/50000000000000 : ℝ), (3777081860043/25000000000000 : ℝ), (12780193001781/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_e004_c05_s0_44 (p : ℝ) (hpa : (13/2 : ℝ) ≤ p) (hpb : p ≤ (53/8 : ℝ)) (x : Fin 3 → ℝ) :
    (38602849/2000000000 : ℝ)*x 0 + (6925139767/10000000000 : ℝ)*x 1 + (200917003/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (53/8 : ℝ)) 53 45 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(38602849/2000000000 : ℝ), (6925139767/10000000000 : ℝ), (200917003/500000000 : ℝ)] ![(478382466133/50000000000000 : ℝ), (12974489521613/20000000000000 : ℝ), (34170787440641/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem sign_e004_c05_s0 (p : ℝ) (hpa : (13/2 : ℝ) ≤ p) (hpb : p ≤ (53/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (126109/50000 : ℝ) (149157/100000 : ℝ) (2639/3125 : ℝ) X)
    (sign0 : (X 1 1+X 2 1) ≤ 0)
    (sign1 : (X 1 2+X 2 2) ≤ 0)
    (sign2 : (X 0 0+X 2 0) ≤ 0)
    (sign3 : 0 ≤ (X 0 2+X 2 2))
    (sign4 : 0 ≤ (X 0 0+X 1 0))
    (sign5 : 0 ≤ (X 0 1+X 1 1))
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1 : ℝ)*pair X i i) :
    ∀ i h, i ≠ h → |pair X i h| ≤ (11557/25000 : ℝ)*pair X i i := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f (by norm_num)
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
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
  have base3 : ((1 : ℝ)*N 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 1]
  have base7 : ((1 : ℝ)*T) ≤ (149157/100000 : ℝ) := by
    linarith only [f.Tcap]
  have base43 : ((1 : ℝ)*X 1 1+(1 : ℝ)*X 2 1) ≤ (0 : ℝ) := by
    linarith only [sign0]
  have base45 : ((1 : ℝ)*X 1 2+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [sign1]
  have base51 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 2 0) ≤ (0 : ℝ) := by
    linarith only [sign2]
  have base59 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*X 1 0) ≤ (0 : ℝ) := by
    linarith only [sign4]
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
  have hpow : (1 : ℝ) ^ (13/2 : ℝ) ≤ (1 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 13 2 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hcorner1 : (2 : ℝ) ≤ (27813287/25000000 : ℝ) ^ (13/2 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (27813287/25000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 13 2 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hcorner2 : (3 : ℝ) ≤ (15313287/12500000 : ℝ) ^ (13/2 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (15313287/12500000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 13 2 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have major0 : P 0 ≤ (X 1 0+X 2 0)+(2813287/25000000 : ℝ)*(-(X 1 1+X 2 1)+-(X 1 2+X 2 2)) := by
    clear * - p hpa X P hratio hmain hpow hcorner1 hcorner2 sign0 sign1
    have hh := signed_majorant (p := p) (a := (13/2 : ℝ)) (rho := (1 : ℝ)) (alpha := (2813287/25000000 : ℝ))
      (by linarith) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [hpow,hcorner1]) (by linarith only [hpow,hcorner2])
      (hmain 0) (hratio 0 1 (by decide)) (hratio 0 2 (by decide))
    change lpNorm p (pair X 0) ≤ _
    rw [lpNorm_eq3 p _ (i := 0) (j := 1) (k := 2) (by decide) (by decide) (by decide)]
    simp only [pair0,pair1,pair2,Pi.add_apply] at hh ⊢
    simpa only [abs_of_nonpos sign0, abs_of_nonpos sign1] using hh
  have major1 : P 1 ≤ (X 0 1+X 2 1)+(2813287/25000000 : ℝ)*(-(X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    clear * - p hpa X P hratio hmain hpow hcorner1 hcorner2 sign2 sign3
    have hh := signed_majorant (p := p) (a := (13/2 : ℝ)) (rho := (1 : ℝ)) (alpha := (2813287/25000000 : ℝ))
      (by linarith) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [hpow,hcorner1]) (by linarith only [hpow,hcorner2])
      (hmain 1) (hratio 1 0 (by decide)) (hratio 1 2 (by decide))
    change lpNorm p (pair X 1) ≤ _
    rw [lpNorm_eq3 p _ (i := 1) (j := 0) (k := 2) (by decide) (by decide) (by decide)]
    simp only [pair0,pair1,pair2,Pi.add_apply] at hh ⊢
    simpa only [abs_of_nonpos sign2, abs_of_nonneg sign3] using hh
  have major2 : P 2 ≤ (X 0 2+X 1 2)+(2813287/25000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    clear * - p hpa X P hratio hmain hpow hcorner1 hcorner2 sign4 sign5
    have hh := signed_majorant (p := p) (a := (13/2 : ℝ)) (rho := (1 : ℝ)) (alpha := (2813287/25000000 : ℝ))
      (by linarith) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [hpow,hcorner1]) (by linarith only [hpow,hcorner2])
      (hmain 2) (hratio 2 0 (by decide)) (hratio 2 1 (by decide))
    change lpNorm p (pair X 2) ≤ _
    rw [lpNorm_eq3 p _ (i := 2) (j := 0) (k := 1) (by decide) (by decide) (by decide)]
    simp only [pair0,pair1,pair2,Pi.add_apply] at hh ⊢
    simpa only [abs_of_nonneg sign4, abs_of_nonneg sign5] using hh
  have sp0 : ((-50191541/5000000000 : ℝ)*X 0 0+(55305887/100000000 : ℝ)*X 0 1+(5530588593/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_e004_c05_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((684882307/1000000000 : ℝ)*X 1 0+(-466008421/2000000000 : ℝ)*X 1 1+(2330042133/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_e004_c05_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2698462237/5000000000 : ℝ)*X 2 0+(3167265437/10000000000 : ℝ)*X 2 1+(-791816369/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_e004_c05_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((-39108231/5000000000 : ℝ)*X 0 0+(1383977143/2500000000 : ℝ)*X 0 1+(2767954279/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_e004_c05_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((661041437/1250000000 : ℝ)*X 2 0+(334671323/1250000000 : ℝ)*X 2 1+(-3759897457/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_e004_c05_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((6818584823/10000000000 : ℝ)*X 1 0+(-344882543/1250000000 : ℝ)*X 1 1+(1924337049/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_e004_c05_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp16 : ((1315455683/2500000000 : ℝ)*X 2 0+(1409527991/5000000000 : ℝ)*X 2 1+(-3653778563/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_e004_c05_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp17 : ((1999999997/2000000000 : ℝ)*X 1 0+(-367/10000000000 : ℝ)*X 1 2+(1999999997/2000000000 : ℝ)*X 2 0+(-367/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    have hh := support_e004_c05_s0_17 p hpa hpb (pair X 0)
    change _ ≤ P 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp21 : ((-367131539/10000000000 : ℝ)*X 0 0+(2673642887/5000000000 : ℝ)*X 0 1+(27813287/50000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_e004_c05_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp23 : ((27457393/78125000 : ℝ)*X 2 0+(2019170171/5000000000 : ℝ)*X 2 1+(-2122172291/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_e004_c05_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp27 : ((-104894877/10000000000 : ℝ)*X 0 0+(808771193/2000000000 : ℝ)*X 0 1+(6946390817/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_e004_c05_s0_27 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp28 : ((1617170577/2000000000 : ℝ)*X 1 0+(-377045669/2000000000 : ℝ)*X 1 1+(1186856823/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_e004_c05_s0_28 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp29 : ((320608039/500000000 : ℝ)*X 2 0+(1560483879/5000000000 : ℝ)*X 2 1+(-2039720097/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_e004_c05_s0_29 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp32 : ((113662697/5000000000 : ℝ)*X 0 0+(496822337/1250000000 : ℝ)*X 0 1+(6946390817/10000000000 : ℝ)*X 0 2+(113662697/5000000000 : ℝ)*X 1 0+(496822337/1250000000 : ℝ)*X 1 1+(6946390817/10000000000 : ℝ)*X 1 2+(113662697/5000000000 : ℝ)*X 2 0+(496822337/1250000000 : ℝ)*X 2 1+(6946390817/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_e004_c05_s0_32 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp33 : ((-154709819/10000000000 : ℝ)*X 0 0+(5636416707/10000000000 : ℝ)*X 0 1+(5396526387/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_e004_c05_s0_33 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp34 : ((8498058603/10000000000 : ℝ)*X 1 0+(-10413211/80000000 : ℝ)*X 1 1+(304714821/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_e004_c05_s0_34 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp35 : ((3532837489/10000000000 : ℝ)*X 2 0+(2116429441/5000000000 : ℝ)*X 2 1+(-806414243/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_e004_c05_s0_35 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp38 : ((232124837/2000000000 : ℝ)*X 0 0+(1052869577/2000000000 : ℝ)*X 0 1+(5087651507/10000000000 : ℝ)*X 0 2+(232124837/2000000000 : ℝ)*X 1 0+(1052869577/2000000000 : ℝ)*X 1 1+(5087651507/10000000000 : ℝ)*X 1 2+(232124837/2000000000 : ℝ)*X 2 0+(1052869577/2000000000 : ℝ)*X 2 1+(5087651507/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_e004_c05_s0_38 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp39 : ((-125811339/10000000000 : ℝ)*X 0 0+(3479729519/5000000000 : ℝ)*X 0 1+(200917003/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_e004_c05_s0_39 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp40 : ((8079628369/10000000000 : ℝ)*X 1 0+(-606014373/5000000000 : ℝ)*X 1 1+(1870052947/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_e004_c05_s0_40 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp41 : ((3209778683/5000000000 : ℝ)*X 2 0+(251199209/1250000000 : ℝ)*X 2 1+(-3140445027/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_e004_c05_s0_41 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp44 : ((38602849/2000000000 : ℝ)*X 0 0+(6925139767/10000000000 : ℝ)*X 0 1+(200917003/500000000 : ℝ)*X 0 2+(38602849/2000000000 : ℝ)*X 1 0+(6925139767/10000000000 : ℝ)*X 1 1+(200917003/500000000 : ℝ)*X 1 2+(38602849/2000000000 : ℝ)*X 2 0+(6925139767/10000000000 : ℝ)*X 2 1+(200917003/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_e004_c05_s0_44 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have r0 : (0 : ℝ) ≤ ((11557/25000 : ℝ)*X 1 0+(1 : ℝ)*X 1 1+(11557/25000 : ℝ)*X 2 0+(1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (2574859288860597807921/5000000000000000000000 : ℝ) := by norm_num
    linear_combination (283920770971/200000000000 : ℝ)*(base1) + (97811407007/250000000000 : ℝ)*(base7) + (1528004836211/1000000000000 : ℝ)*(base45) + (103474295923/500000000000 : ℝ)*(base51) + (166178464063/1000000000000 : ℝ)*(base59) + (129685227627/50000000000 : ℝ)*(major0) + (129685227627/50000000000 : ℝ)*(major1) + (129685227627/50000000000 : ℝ)*(major2) + (216661044803/200000000000 : ℝ)*(sp1) + (2606237004119/500000000000 : ℝ)*(sp7) + (844467422877/500000000000 : ℝ)*(sp9) + (2709564954509/1000000000000 : ℝ)*(sp15) + (210393533277/100000000000 : ℝ)*(sp23) + (12571/500000000000 : ℝ)*(sp27) + (257089556707/250000000000 : ℝ)*(f.failure) + (948217544631/250000000000 : ℝ)*(f.sum) + (139778851/1000000000000000000000 : ℝ)*base66 + (964948083/5000000000000000000000 : ℝ)*base68 + (1412514909/5000000000000000000000 : ℝ)*base70 + (2563250957/10000000000000000000000 : ℝ)*base72 + (646957329/10000000000000000000000 : ℝ)*base74 + (6791719/39062500000000000000 : ℝ)*base75 + (297922371/625000000000000000000 : ℝ)*base77 + (184475081/2500000000000000000000 : ℝ)*base79 + (65800141/5000000000000000000000 : ℝ)*base82 + (1/1000000000000 : ℝ)*base83 + (13063/12500000000000000 : ℝ)*base89 + (13063/12500000000000000 : ℝ)*base91 + (13063/12500000000000000 : ℝ)*base93 + (1/1000000000000 : ℝ)*base96 + hcertificate_margin
  have out0 : |(X 1 1+X 2 1)| ≤ (11557/25000 : ℝ)*(X 1 0+X 2 0) := by
    rw [abs_of_nonpos sign0]
    linarith only [r0]
  have r1 : (0 : ℝ) ≤ ((11557/25000 : ℝ)*X 1 0+(1 : ℝ)*X 1 2+(11557/25000 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (5483368801218570111663/10000000000000000000000 : ℝ) := by norm_num
    linear_combination (1083691858837/1000000000000 : ℝ)*(base1) + (100776478091/250000000000 : ℝ)*(base7) + (582384638883/1000000000000 : ℝ)*(base43) + (51948529297/250000000000 : ℝ)*(base51) + (34626313077/200000000000 : ℝ)*(base59) + (68662410499/40000000000 : ℝ)*(major0) + (68662410499/40000000000 : ℝ)*(major1) + (68662410499/40000000000 : ℝ)*(major2) + (13488387193/3906250000 : ℝ)*(sp0) + (1662616789081/1000000000000 : ℝ)*(sp1) + (116165050853/1000000000000 : ℝ)*(sp9) + (706718600783/1000000000000 : ℝ)*(sp15) + (2253170339011/1000000000000 : ℝ)*(sp23) + (63647/500000000000 : ℝ)*(sp27) + (680585946473/1000000000000 : ℝ)*(f.failure) + (296166923733/125000000000 : ℝ)*(f.sum) + (494153853/5000000000000000000000 : ℝ)*base66 + (621196831/1000000000000000000000 : ℝ)*base68 + (3790714071/5000000000000000000000 : ℝ)*base70 + (3034485079/10000000000000000000000 : ℝ)*base72 + (3823095143/10000000000000000000000 : ℝ)*base74 + (53689457/500000000000000000000 : ℝ)*base76 + (137404821/1250000000000000000000 : ℝ)*base77 + (1813059957/5000000000000000000000 : ℝ)*base80 + (1088530777/10000000000000000000000 : ℝ)*base82 + (1/1000000000000 : ℝ)*base83 + (13557/50000000000000000 : ℝ)*base89 + (13557/50000000000000000 : ℝ)*base91 + (13557/50000000000000000 : ℝ)*base93 + hcertificate_margin
  have out1 : |(X 1 2+X 2 2)| ≤ (11557/25000 : ℝ)*(X 1 0+X 2 0) := by
    rw [abs_of_nonpos sign1]
    linarith only [r1]
  have r2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(11557/25000 : ℝ)*X 0 1+(1 : ℝ)*X 2 0+(11557/25000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (675319131147001951053/1250000000000000000000 : ℝ) := by norm_num
    linear_combination (19738915491/1000000000000 : ℝ)*(base3) + (159232856283/100000000000 : ℝ)*(base45) + (84420213819/100000000000 : ℝ)*(base59) + (2620655798823/500000000000 : ℝ)*(major0) + (587053056113/125000000000 : ℝ)*(major1) + (587053056113/125000000000 : ℝ)*(major2) + (406290648883/250000000000 : ℝ)*(sp2) + (89084931897/100000000000 : ℝ)*(sp16) + (544887148741/1000000000000 : ℝ)*(sp17) + (7350714121313/1000000000000 : ℝ)*(sp21) + (534410878489/500000000000 : ℝ)*(sp32) + (483470220681/100000000000 : ℝ)*(sp35) + (773489002377/1000000000000 : ℝ)*(sp38) + (1842613259201/250000000000 : ℝ)*(sp40) + (931024837423/500000000000 : ℝ)*(f.failure) + (7350714121313/1000000000000 : ℝ)*(f.sum) + (439039637/1000000000000000000000 : ℝ)*base66 + (913637079/2000000000000000000000 : ℝ)*base68 + (1159538033/2000000000000000000000 : ℝ)*base70 + (978965281/5000000000000000000000 : ℝ)*base71 + (101922851/10000000000000000000000 : ℝ)*base73 + (1290268703/5000000000000000000000 : ℝ)*base76 + (512484427/500000000000000000000 : ℝ)*base77 + (285216577/10000000000000000000000 : ℝ)*base80 + (1138614663/5000000000000000000000 : ℝ)*base82 + (1/1000000000000 : ℝ)*base88 + (47893/25000000000000000 : ℝ)*base90 + (22893/25000000000000000 : ℝ)*base92 + (22893/25000000000000000 : ℝ)*base94 + hcertificate_margin
  have out2 : |(X 0 0+X 2 0)| ≤ (11557/25000 : ℝ)*(X 0 1+X 2 1) := by
    rw [abs_of_nonpos sign2]
    linarith only [r2]
  have r3 : (0 : ℝ) ≤ ((11557/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(11557/25000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (16376549795584401/2000000000000000000000 : ℝ) := by norm_num
    linear_combination (109789052773/200000000000 : ℝ)*(base1) + (274957619003/250000000000 : ℝ)*(base7) + (155190795767/250000000000 : ℝ)*(base45) + (2436340229/500000000000 : ℝ)*(base51) + (1112682677823/500000000000 : ℝ)*(major0) + (1112682677823/500000000000 : ℝ)*(major1) + (1112682677823/500000000000 : ℝ)*(major2) + (141991/31250000000 : ℝ)*(sp1) + (538751/200000000000 : ℝ)*(sp2) + (3570530316301/1000000000000 : ℝ)*(sp27) + (755395127181/250000000000 : ℝ)*(sp28) + (1510776569559/500000000000 : ℝ)*(sp29) + (1433203427201/1000000000000 : ℝ)*(sp32) + (14609781/500000000000 : ℝ)*(sp41) + (441159107527/500000000000 : ℝ)*(f.failure) + (755396263109/250000000000 : ℝ)*(f.sum) + (2546847783/10000000000000000000000 : ℝ)*base65 + (1290265439/10000000000000000000000 : ℝ)*base67 + (190569833/5000000000000000000000 : ℝ)*base69 + (101192987/5000000000000000000000 : ℝ)*base72 + (250983589/2500000000000000000000 : ℝ)*base74 + (190483113/2000000000000000000000 : ℝ)*base76 + (2149187851/2500000000000000000000 : ℝ)*base77 + (2043514261/10000000000000000000000 : ℝ)*base79 + (4146638217/10000000000000000000000 : ℝ)*base82 + (1/1000000000000 : ℝ)*base88 + (27557/25000000000000000 : ℝ)*base90 + (27557/25000000000000000 : ℝ)*base92 + (27557/25000000000000000 : ℝ)*base94 + hcertificate_margin
  have out3 : |(X 0 2+X 2 2)| ≤ (11557/25000 : ℝ)*(X 0 1+X 2 1) := by
    rw [abs_of_nonneg sign3]
    linarith only [r3]
  have r4 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(11557/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(11557/25000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (2610904011366879231387/5000000000000000000000 : ℝ) := by norm_num
    linear_combination (772369488281/500000000000 : ℝ)*(base45) + (989689006097/1000000000000 : ℝ)*(base51) + (6828907593819/1000000000000 : ℝ)*(major0) + (4543388039247/1000000000000 : ℝ)*(major1) + (4543388039247/1000000000000 : ℝ)*(major2) + (861095555193/500000000000 : ℝ)*(sp2) + (571379888643/250000000000 : ℝ)*(sp17) + (275598636099/62500000000 : ℝ)*(sp21) + (2397710110499/500000000000 : ℝ)*(sp28) + (498293267707/500000000000 : ℝ)*(sp33) + (1157961079721/500000000000 : ℝ)*(sp34) + (2694575635027/500000000000 : ℝ)*(sp35) + (900686715311/500000000000 : ℝ)*(sp38) + (852588833721/500000000000 : ℝ)*(sp39) + (900686715311/500000000000 : ℝ)*(f.failure) + (177783559511/25000000000 : ℝ)*(f.sum) + (357181639/1000000000000000000000 : ℝ)*base66 + (98043569/500000000000000000000 : ℝ)*base68 + (601827273/2500000000000000000000 : ℝ)*base70 + (2165588823/5000000000000000000000 : ℝ)*base72 + (284312099/1000000000000000000000 : ℝ)*base73 + (516866311/1250000000000000000000 : ℝ)*base75 + (366133573/500000000000000000000 : ℝ)*base78 + (45660199/500000000000000000000 : ℝ)*base80 + (1931686079/2500000000000000000000 : ℝ)*base81 + (20101/25000000000000000 : ℝ)*base90 + (20101/25000000000000000 : ℝ)*base92 + (20101/25000000000000000 : ℝ)*base94 + hcertificate_margin
  have out4 : |(X 0 0+X 1 0)| ≤ (11557/25000 : ℝ)*(X 0 2+X 1 2) := by
    rw [abs_of_nonneg sign4]
    linarith only [r4]
  have r5 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 1+(11557/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 1+(11557/25000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (7065203765586552957/10000000000000000000000 : ℝ) := by norm_num
    linear_combination (7408910043/500000000000 : ℝ)*(base1) + (552767420993/500000000000 : ℝ)*(base7) + (152866617853/1000000000000 : ℝ)*(base45) + (2060803/250000000000 : ℝ)*(base51) + (1109801744379/500000000000 : ℝ)*(major0) + (1109801744379/500000000000 : ℝ)*(major1) + (1109801744379/500000000000 : ℝ)*(major2) + (352749759/1000000000000 : ℝ)*(sp1) + (191041281/500000000000 : ℝ)*(sp2) + (1210983579/500000000000 : ℝ)*(sp29) + (3024094686521/1000000000000 : ℝ)*(sp39) + (3008924116677/1000000000000 : ℝ)*(sp40) + (751618204179/250000000000 : ℝ)*(sp41) + (123171922381/62500000000 : ℝ)*(sp44) + (220008434049/250000000000 : ℝ)*(f.failure) + (752319216609/250000000000 : ℝ)*(f.sum) + (3084815901/10000000000000000000000 : ℝ)*base66 + (134601203/1000000000000000000000 : ℝ)*base68 + (99571931/500000000000000000000 : ℝ)*base70 + (5197409063/10000000000000000000000 : ℝ)*base72 + (34759221/2000000000000000000000 : ℝ)*base73 + (2804218613/5000000000000000000000 : ℝ)*base76 + (1743977901/2500000000000000000000 : ℝ)*base78 + (1631572271/5000000000000000000000 : ℝ)*base80 + (203065059/1000000000000000000000 : ℝ)*base82 + (1/1000000000000 : ℝ)*base84 + (10341/12500000000000000 : ℝ)*base89 + (10341/12500000000000000 : ℝ)*base91 + (10341/12500000000000000 : ℝ)*base93 + hcertificate_margin
  have out5 : |(X 0 1+X 1 1)| ≤ (11557/25000 : ℝ)*(X 0 2+X 1 2) := by
    rw [abs_of_nonneg sign5]
    linarith only [r5]
  intro i h hij
  fin_cases i <;> fin_cases h <;> try contradiction
  · change |pair X 0 1| ≤ (11557/25000 : ℝ)*pair X 0 0
    simpa only [pair0,pair1,pair2,Pi.add_apply] using out0
  · change |pair X 0 2| ≤ (11557/25000 : ℝ)*pair X 0 0
    simpa only [pair0,pair1,pair2,Pi.add_apply] using out1
  · change |pair X 1 0| ≤ (11557/25000 : ℝ)*pair X 1 1
    simpa only [pair0,pair1,pair2,Pi.add_apply] using out2
  · change |pair X 1 2| ≤ (11557/25000 : ℝ)*pair X 1 1
    simpa only [pair0,pair1,pair2,Pi.add_apply] using out3
  · change |pair X 2 0| ≤ (11557/25000 : ℝ)*pair X 2 2
    simpa only [pair0,pair1,pair2,Pi.add_apply] using out4
  · change |pair X 2 1| ≤ (11557/25000 : ℝ)*pair X 2 2
    simpa only [pair0,pair1,pair2,Pi.add_apply] using out5

end HlawkaSchatten.DiagonalCutoff6


open HlawkaSchatten HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem solution (p : ℝ) (hpa : (13/2 : ℝ) ≤ p) (hpb : p ≤ (53/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (126109/50000 : ℝ) (149157/100000 : ℝ) (2639/3125 : ℝ) X)
    (sign0 : (X 1 1+X 2 1) ≤ 0)
    (sign1 : (X 1 2+X 2 2) ≤ 0)
    (sign2 : (X 0 0+X 2 0) ≤ 0)
    (sign3 : 0 ≤ (X 0 2+X 2 2))
    (sign4 : 0 ≤ (X 0 0+X 1 0))
    (sign5 : 0 ≤ (X 0 1+X 1 1))
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1 : ℝ)*pair X i i) :
    ∀ i h, i ≠ h → |pair X i h| ≤ (11557/25000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff6.sign_e004_c05_s0 p hpa hpb X hX sign0 sign1 sign2 sign3 sign4 sign5 hratio

#print axioms solution
