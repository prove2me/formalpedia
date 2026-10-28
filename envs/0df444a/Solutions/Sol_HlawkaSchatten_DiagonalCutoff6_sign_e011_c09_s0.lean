-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff6.sign_e011_c09_s0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-27T19:38:17.162494+00:00
-- url     : https://prove2.me/submissions/2922d928-7450-41a3-b78a-06d7f1924ce2

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
theorem support_e011_c09_s0_0 (p : ℝ) (hpa : (59/8 : ℝ) ≤ p) (hpb : p ≤ (15/2 : ℝ)) (x : Fin 3 → ℝ) :
    (-626623797/5000000000 : ℝ)*x 0 + (290624813/500000000 : ℝ)*x 1 + (426652419/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (15/2 : ℝ)) 15 13 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(-626623797/5000000000 : ℝ), (290624813/500000000 : ℝ), (426652419/1000000000 : ℝ)] ![(1820972210613/20000000000000 : ℝ), (3341879678251/6250000000000 : ℝ), (37425064082963/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_e011_c09_s0_2 (p : ℝ) (hpa : (59/8 : ℝ) ≤ p) (hpb : p ≤ (15/2 : ℝ)) (x : Fin 3 → ℝ) :
    (2839091461/5000000000 : ℝ)*x 0 + (4266522981/10000000000 : ℝ)*x 1 + (-710671733/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (15/2 : ℝ)) 15 13 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(2839091461/5000000000 : ℝ), (4266522981/10000000000 : ℝ), (-710671733/5000000000 : ℝ)] ![(6505871041461/12500000000000 : ℝ), (37425051846313/100000000000000 : ℝ), (10527979803031/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_e011_c09_s0_7 (p : ℝ) (hpa : (59/8 : ℝ) ≤ p) (hpb : p ≤ (15/2 : ℝ)) (x : Fin 3 → ℝ) :
    (-1339650269/10000000000 : ℝ)*x 0 + (7120259187/10000000000 : ℝ)*x 1 + (1377278861/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (15/2 : ℝ)) 15 13 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(-1339650269/10000000000 : ℝ), (7120259187/10000000000 : ℝ), (1377278861/5000000000 : ℝ)] ![(614557386709/6250000000000 : ℝ), (33788806656167/50000000000000 : ℝ), (22589468490091/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_e011_c09_s0_8 (p : ℝ) (hpa : (59/8 : ℝ) ≤ p) (hpb : p ≤ (15/2 : ℝ)) (x : Fin 3 → ℝ) :
    (5391012763/10000000000 : ℝ)*x 0 + (-419730463/1250000000 : ℝ)*x 1 + (1377278631/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (15/2 : ℝ)) 15 13 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(5391012763/10000000000 : ℝ), (-419730463/1250000000 : ℝ), (1377278631/5000000000 : ℝ)] ![(490217574611/1000000000000 : ℝ), (14194389196437/50000000000000 : ℝ), (22589464137379/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_e011_c09_s0_9 (p : ℝ) (hpa : (59/8 : ℝ) ≤ p) (hpb : p ≤ (15/2 : ℝ)) (x : Fin 3 → ℝ) :
    (1347753269/2500000000 : ℝ)*x 0 + (1377278857/5000000000 : ℝ)*x 1 + (-209865183/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (15/2 : ℝ)) 15 13 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(1347753269/2500000000 : ℝ), (1377278857/5000000000 : ℝ), (-209865183/625000000 : ℝ)] ![(49021760745157/100000000000000 : ℝ), (22589468414391/100000000000000 : ℝ), (227110166583/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_e011_c09_s0_13 (p : ℝ) (hpa : (59/8 : ℝ) ≤ p) (hpb : p ≤ (15/2 : ℝ)) (x : Fin 3 → ℝ) :
    (6699049/10000000000 : ℝ)*x 0 + (26907601/400000000 : ℝ)*x 1 + (4806029197/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (15/2 : ℝ)) 15 13 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(6699049/10000000000 : ℝ), (26907601/400000000 : ℝ), (4806029197/5000000000 : ℝ)] ![(10881217473/50000000000000 : ℝ), (4440980150633/100000000000000 : ℝ), (19107451481843/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_e011_c09_s0_14 (p : ℝ) (hpa : (59/8 : ℝ) ≤ p) (hpb : p ≤ (15/2 : ℝ)) (x : Fin 3 → ℝ) :
    (-2449468997/10000000000 : ℝ)*x 0 + (7173087999/10000000000 : ℝ)*x 1 + (802663307/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (15/2 : ℝ)) 15 13 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(-2449468997/10000000000 : ℝ), (7173087999/10000000000 : ℝ), (802663307/5000000000 : ℝ)] ![(19727998022137/100000000000000 : ℝ), (34078236346721/50000000000000 : ℝ), (12115529272037/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_e011_c09_s0_15 (p : ℝ) (hpa : (59/8 : ℝ) ≤ p) (hpb : p ≤ (15/2 : ℝ)) (x : Fin 3 → ℝ) :
    (2037374473/5000000000 : ℝ)*x 0 + (-916360341/10000000000 : ℝ)*x 1 + (6252290789/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (15/2 : ℝ)) 15 13 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(2037374473/5000000000 : ℝ), (-916360341/10000000000 : ℝ), (6252290789/10000000000 : ℝ)] ![(35490847683713/100000000000000 : ℝ), (6344306779943/100000000000000 : ℝ), (454412855681/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_e011_c09_s0_16 (p : ℝ) (hpa : (59/8 : ℝ) ≤ p) (hpb : p ≤ (15/2 : ℝ)) (x : Fin 3 → ℝ) :
    (5020318863/10000000000 : ℝ)*x 0 + (5721768509/10000000000 : ℝ)*x 1 + (-12057361/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (15/2 : ℝ)) 15 13 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(5020318863/10000000000 : ℝ), (5721768509/10000000000 : ℝ), (-12057361/312500000 : ℝ)] ![(45153348649267/100000000000000 : ℝ), (52508214391441/100000000000000 : ℝ), (2338436946941/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_e011_c09_s0_20 (p : ℝ) (hpa : (59/8 : ℝ) ≤ p) (hpb : p ≤ (15/2 : ℝ)) (x : Fin 3 → ℝ) :
    (9270589/1250000000 : ℝ)*x 0 + (1292586617/10000000000 : ℝ)*x 1 + (4573145207/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (15/2 : ℝ)) 15 13 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(9270589/1250000000 : ℝ), (1292586617/10000000000 : ℝ), (4573145207/5000000000 : ℝ)] ![(174383490891/50000000000000 : ℝ), (9435417908557/100000000000000 : ℝ), (22553953775733/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_e011_c09_s0_21 (p : ℝ) (hpa : (59/8 : ℝ) ≤ p) (hpb : p ≤ (15/2 : ℝ)) (x : Fin 3 → ℝ) :
    (-2035302131/5000000000 : ℝ)*x 0 + (4859016247/10000000000 : ℝ)*x 1 + (2592945987/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (15/2 : ℝ)) 15 13 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(-2035302131/5000000000 : ℝ), (4859016247/10000000000 : ℝ), (2592945987/10000000000 : ℝ)] ![(17724598561331/50000000000000 : ℝ), (679430512447/1562500000000 : ℝ), (2633406257631/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_e011_c09_s0_22 (p : ℝ) (hpa : (59/8 : ℝ) ≤ p) (hpb : p ≤ (15/2 : ℝ)) (x : Fin 3 → ℝ) :
    (3416247303/5000000000 : ℝ)*x 0 + (-1430174963/10000000000 : ℝ)*x 1 + (3003422859/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (15/2 : ℝ)) 15 13 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(3416247303/5000000000 : ℝ), (-1430174963/10000000000 : ℝ), (3003422859/10000000000 : ℝ)] ![(64436205613299/100000000000000 : ℝ), (1325436897651/12500000000000 : ℝ), (24960299188783/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_e011_c09_s0_23 (p : ℝ) (hpa : (59/8 : ℝ) ≤ p) (hpb : p ≤ (15/2 : ℝ)) (x : Fin 3 → ℝ) :
    (3611309759/10000000000 : ℝ)*x 0 + (4134408829/10000000000 : ℝ)*x 1 + (-191453601/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (15/2 : ℝ)) 15 13 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(3611309759/10000000000 : ℝ), (4134408829/10000000000 : ℝ), (-191453601/500000000 : ℝ)] ![(30875440562497/100000000000000 : ℝ), (18045549187583/50000000000000 : ℝ), (3303346104389/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_e011_c09_s0_27 (p : ℝ) (hpa : (59/8 : ℝ) ≤ p) (hpb : p ≤ (15/2 : ℝ)) (x : Fin 3 → ℝ) :
    (1143/2500000000 : ℝ)*x 0 + (2262303821/10000000000 : ℝ)*x 1 + (84199477/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (15/2 : ℝ)) 15 13 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(1143/2500000000 : ℝ), (2262303821/10000000000 : ℝ), (84199477/100000000 : ℝ)] ![(1209701/25000000000000 : ℝ), (1124944480761/6250000000000 : ℝ), (16400176693293/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_e011_c09_s0_28 (p : ℝ) (hpa : (59/8 : ℝ) ≤ p) (hpb : p ≤ (15/2 : ℝ)) (x : Fin 3 → ℝ) :
    (-3800901/25000000 : ℝ)*x 0 + (775958079/2000000000 : ℝ)*x 1 + (2982050509/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (15/2 : ℝ)) 15 13 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(-3800901/25000000 : ℝ), (775958079/2000000000 : ℝ), (2982050509/5000000000 : ℝ)] ![(2844671887587/25000000000000 : ℝ), (33538836811251/100000000000000 : ℝ), (55082475620093/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_e011_c09_s0_29 (p : ℝ) (hpa : (59/8 : ℝ) ≤ p) (hpb : p ≤ (15/2 : ℝ)) (x : Fin 3 → ℝ) :
    (93810719/125000000 : ℝ)*x 0 + (-51167067/200000000 : ℝ)*x 1 + (526636829/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (15/2 : ℝ)) 15 13 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(93810719/125000000 : ℝ), (-51167067/200000000 : ℝ), (526636829/5000000000 : ℝ)] ![(35903300294137/50000000000000 : ℝ), (1037164243469/5000000000000 : ℝ), (3725057266519/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_e011_c09_s0_30 (p : ℝ) (hpa : (59/8 : ℝ) ≤ p) (hpb : p ≤ (15/2 : ℝ)) (x : Fin 3 → ℝ) :
    (1500971277/2000000000 : ℝ)*x 0 + (102155383/400000000 : ℝ)*x 1 + (-132299389/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (15/2 : ℝ)) 15 13 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(1500971277/2000000000 : ℝ), (102155383/400000000 : ℝ), (-132299389/1250000000 : ℝ)] ![(71806588057853/100000000000000 : ℝ), (2587685383309/12500000000000 : ℝ), (7491928858677/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_e011_c09_s0_34 (p : ℝ) (hpa : (59/8 : ℝ) ≤ p) (hpb : p ≤ (15/2 : ℝ)) (x : Fin 3 → ℝ) :
    (2619519/10000000000 : ℝ)*x 0 + (2578087961/10000000000 : ℝ)*x 1 + (4079007847/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (15/2 : ℝ)) 15 13 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(2619519/10000000000 : ℝ), (2578087961/10000000000 : ℝ), (4079007847/5000000000 : ℝ)] ![(460318821/6250000000000 : ℝ), (654000638973/3125000000000 : ℝ), (19766153610871/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_e011_c09_s0_35 (p : ℝ) (hpa : (59/8 : ℝ) ≤ p) (hpb : p ≤ (15/2 : ℝ)) (x : Fin 3 → ℝ) :
    (-768174737/2000000000 : ℝ)*x 0 + (4550805707/10000000000 : ℝ)*x 1 + (3166674349/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (15/2 : ℝ)) 15 13 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(-768174737/2000000000 : ℝ), (4550805707/10000000000 : ℝ), (3166674349/10000000000 : ℝ)] ![(16575482785217/50000000000000 : ℝ), (5039605092793/12500000000000 : ℝ), (13266096832299/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_e011_c09_s0_36 (p : ℝ) (hpa : (59/8 : ℝ) ≤ p) (hpb : p ≤ (15/2 : ℝ)) (x : Fin 3 → ℝ) :
    (2816528637/10000000000 : ℝ)*x 0 + (-24493207/62500000 : ℝ)*x 1 + (600230801/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (15/2 : ℝ)) 15 13 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(2816528637/10000000000 : ℝ), (-24493207/62500000 : ℝ), (600230801/1250000000 : ℝ)] ![(11588435752769/50000000000000 : ℝ), (8482341280437/25000000000000 : ℝ), (8578752670883/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_e011_c09_s0_37 (p : ℝ) (hpa : (59/8 : ℝ) ≤ p) (hpb : p ≤ (15/2 : ℝ)) (x : Fin 3 → ℝ) :
    (7090486789/10000000000 : ℝ)*x 0 + (3171574049/10000000000 : ℝ)*x 1 + (-894343531/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (15/2 : ℝ)) 15 13 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(7090486789/10000000000 : ℝ), (3171574049/10000000000 : ℝ), (-894343531/10000000000 : ℝ)] ![(3362583994611/5000000000000 : ℝ), (13289783764653/50000000000000 : ℝ), (3084376278121/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_e011_c09_s0_41 (p : ℝ) (hpa : (59/8 : ℝ) ≤ p) (hpb : p ≤ (15/2 : ℝ)) (x : Fin 3 → ℝ) :
    (859/5000000000 : ℝ)*x 0 + (4550805707/10000000000 : ℝ)*x 1 + (799186673/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (15/2 : ℝ)) 15 13 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(859/5000000000 : ℝ), (4550805707/10000000000 : ℝ), (799186673/1250000000 : ℝ)] ![(62563/4000000000000 : ℝ), (5039605092793/12500000000000 : ℝ), (59683157675699/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_e011_c09_s0_42 (p : ℝ) (hpa : (59/8 : ℝ) ≤ p) (hpb : p ≤ (15/2 : ℝ)) (x : Fin 3 → ℝ) :
    (-1429629757/10000000000 : ℝ)*x 0 + (7275230259/10000000000 : ℝ)*x 1 + (2491986251/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (15/2 : ℝ)) 15 13 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(-1429629757/10000000000 : ℝ), (7275230259/10000000000 : ℝ), (2491986251/10000000000 : ℝ)] ![(10598831212061/100000000000000 : ℝ), (69277530141709/100000000000000 : ℝ), (2515454828523/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_e011_c09_s0_43 (p : ℝ) (hpa : (59/8 : ℝ) ≤ p) (hpb : p ≤ (15/2 : ℝ)) (x : Fin 3 → ℝ) :
    (7457245253/10000000000 : ℝ)*x 0 + (-777032241/10000000000 : ℝ)*x 1 + (284778313/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (15/2 : ℝ)) 15 13 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(7457245253/10000000000 : ℝ), (-777032241/10000000000 : ℝ), (284778313/1000000000 : ℝ)] ![(71281217234743/100000000000000 : ℝ), (5244901697479/100000000000000 : ℝ), (23473881052603/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_e011_c09_s0_44 (p : ℝ) (hpa : (59/8 : ℝ) ≤ p) (hpb : p ≤ (15/2 : ℝ)) (x : Fin 3 → ℝ) :
    (3728624241/5000000000 : ℝ)*x 0 + (709877643/5000000000 : ℝ)*x 1 + (-1142321309/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (15/2 : ℝ)) 15 13 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(3728624241/5000000000 : ℝ), (709877643/5000000000 : ℝ), (-1142321309/5000000000 : ℝ)] ![(71281252848079/100000000000000 : ℝ), (10514407414199/100000000000000 : ℝ), (18204339717983/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_e011_c09_s0_48 (p : ℝ) (hpa : (59/8 : ℝ) ≤ p) (hpb : p ≤ (15/2 : ℝ)) (x : Fin 3 → ℝ) :
    (3007877/10000000000 : ℝ)*x 0 + (1657643197/2500000000 : ℝ)*x 1 + (4298351289/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (15/2 : ℝ)) 15 13 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(3007877/10000000000 : ℝ), (1657643197/2500000000 : ℝ), (4298351289/10000000000 : ℝ)] ![(8638810157/100000000000000 : ℝ), (12448796211097/20000000000000 : ℝ), (37747380122089/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem sign_e011_c09_s0 (p : ℝ) (hpa : (59/8 : ℝ) ≤ p) (hpb : p ≤ (15/2 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (145371/50000 : ℝ) (18063/12500 : ℝ) (43079/50000 : ℝ) X)
    (sign0 : (X 1 1+X 2 1) ≤ 0)
    (sign1 : 0 ≤ (X 1 2+X 2 2))
    (sign2 : (X 0 0+X 2 0) ≤ 0)
    (sign3 : 0 ≤ (X 0 2+X 2 2))
    (sign4 : (X 0 0+X 1 0) ≤ 0)
    (sign5 : 0 ≤ (X 0 1+X 1 1))
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1 : ℝ)*pair X i i) :
    ∀ i h, i ≠ h → |pair X i h| ≤ (44391/100000 : ℝ)*pair X i i := by
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
  have base7 : ((1 : ℝ)*T) ≤ (18063/12500 : ℝ) := by
    linarith only [f.Tcap]
  have base16 : ((-1 : ℝ)*X 1 1+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 1).1]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base34 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 2+(1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 1, f.sum]
  have base43 : ((1 : ℝ)*X 1 1+(1 : ℝ)*X 2 1) ≤ (0 : ℝ) := by
    linarith only [sign0]
  have base57 : ((-1 : ℝ)*N 2+(1 : ℝ)*P 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ptotal 2]
  have base59 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 1 0) ≤ (0 : ℝ) := by
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
  have hpow : (1 : ℝ) ^ (59/8 : ℝ) ≤ (1 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 59 8 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hcorner1 : (2 : ℝ) ≤ (27463611/25000000 : ℝ) ^ (59/8 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (27463611/25000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 59 8 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hcorner2 : (3 : ℝ) ≤ (14963611/12500000 : ℝ) ^ (59/8 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (14963611/12500000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 59 8 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have major0 : P 0 ≤ (X 1 0+X 2 0)+(2463611/25000000 : ℝ)*(-(X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    clear * - p hpa X P hratio hmain hpow hcorner1 hcorner2 sign0 sign1
    have hh := signed_majorant (p := p) (a := (59/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (2463611/25000000 : ℝ))
      (by linarith) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [hpow,hcorner1]) (by linarith only [hpow,hcorner2])
      (hmain 0) (hratio 0 1 (by decide)) (hratio 0 2 (by decide))
    change lpNorm p (pair X 0) ≤ _
    rw [lpNorm_eq3 p _ (i := 0) (j := 1) (k := 2) (by decide) (by decide) (by decide)]
    simp only [pair0,pair1,pair2,Pi.add_apply] at hh ⊢
    simpa only [abs_of_nonpos sign0, abs_of_nonneg sign1] using hh
  have major1 : P 1 ≤ (X 0 1+X 2 1)+(2463611/25000000 : ℝ)*(-(X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    clear * - p hpa X P hratio hmain hpow hcorner1 hcorner2 sign2 sign3
    have hh := signed_majorant (p := p) (a := (59/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (2463611/25000000 : ℝ))
      (by linarith) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [hpow,hcorner1]) (by linarith only [hpow,hcorner2])
      (hmain 1) (hratio 1 0 (by decide)) (hratio 1 2 (by decide))
    change lpNorm p (pair X 1) ≤ _
    rw [lpNorm_eq3 p _ (i := 1) (j := 0) (k := 2) (by decide) (by decide) (by decide)]
    simp only [pair0,pair1,pair2,Pi.add_apply] at hh ⊢
    simpa only [abs_of_nonpos sign2, abs_of_nonneg sign3] using hh
  have major2 : P 2 ≤ (X 0 2+X 1 2)+(2463611/25000000 : ℝ)*(-(X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    clear * - p hpa X P hratio hmain hpow hcorner1 hcorner2 sign4 sign5
    have hh := signed_majorant (p := p) (a := (59/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (2463611/25000000 : ℝ))
      (by linarith) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [hpow,hcorner1]) (by linarith only [hpow,hcorner2])
      (hmain 2) (hratio 2 0 (by decide)) (hratio 2 1 (by decide))
    change lpNorm p (pair X 2) ≤ _
    rw [lpNorm_eq3 p _ (i := 2) (j := 0) (k := 1) (by decide) (by decide) (by decide)]
    simp only [pair0,pair1,pair2,Pi.add_apply] at hh ⊢
    simpa only [abs_of_nonpos sign4, abs_of_nonneg sign5] using hh
  have sp0 : ((-626623797/5000000000 : ℝ)*X 0 0+(290624813/500000000 : ℝ)*X 0 1+(426652419/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_e011_c09_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2839091461/5000000000 : ℝ)*X 2 0+(4266522981/10000000000 : ℝ)*X 2 1+(-710671733/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_e011_c09_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((-1339650269/10000000000 : ℝ)*X 0 0+(7120259187/10000000000 : ℝ)*X 0 1+(1377278861/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_e011_c09_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((5391012763/10000000000 : ℝ)*X 1 0+(-419730463/1250000000 : ℝ)*X 1 1+(1377278631/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_e011_c09_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((1347753269/2500000000 : ℝ)*X 2 0+(1377278857/5000000000 : ℝ)*X 2 1+(-209865183/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_e011_c09_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((6699049/10000000000 : ℝ)*X 0 0+(26907601/400000000 : ℝ)*X 0 1+(4806029197/5000000000 : ℝ)*X 0 2+(6699049/10000000000 : ℝ)*X 1 0+(26907601/400000000 : ℝ)*X 1 1+(4806029197/5000000000 : ℝ)*X 1 2+(6699049/10000000000 : ℝ)*X 2 0+(26907601/400000000 : ℝ)*X 2 1+(4806029197/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_e011_c09_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((-2449468997/10000000000 : ℝ)*X 0 0+(7173087999/10000000000 : ℝ)*X 0 1+(802663307/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_e011_c09_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((2037374473/5000000000 : ℝ)*X 1 0+(-916360341/10000000000 : ℝ)*X 1 1+(6252290789/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_e011_c09_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp16 : ((5020318863/10000000000 : ℝ)*X 2 0+(5721768509/10000000000 : ℝ)*X 2 1+(-12057361/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_e011_c09_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp20 : ((9270589/1250000000 : ℝ)*X 0 0+(1292586617/10000000000 : ℝ)*X 0 1+(4573145207/5000000000 : ℝ)*X 0 2+(9270589/1250000000 : ℝ)*X 1 0+(1292586617/10000000000 : ℝ)*X 1 1+(4573145207/5000000000 : ℝ)*X 1 2+(9270589/1250000000 : ℝ)*X 2 0+(1292586617/10000000000 : ℝ)*X 2 1+(4573145207/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_e011_c09_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp21 : ((-2035302131/5000000000 : ℝ)*X 0 0+(4859016247/10000000000 : ℝ)*X 0 1+(2592945987/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_e011_c09_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp22 : ((3416247303/5000000000 : ℝ)*X 1 0+(-1430174963/10000000000 : ℝ)*X 1 1+(3003422859/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_e011_c09_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp23 : ((3611309759/10000000000 : ℝ)*X 2 0+(4134408829/10000000000 : ℝ)*X 2 1+(-191453601/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_e011_c09_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp27 : ((1143/2500000000 : ℝ)*X 0 0+(2262303821/10000000000 : ℝ)*X 0 1+(84199477/100000000 : ℝ)*X 0 2+(1143/2500000000 : ℝ)*X 1 0+(2262303821/10000000000 : ℝ)*X 1 1+(84199477/100000000 : ℝ)*X 1 2+(1143/2500000000 : ℝ)*X 2 0+(2262303821/10000000000 : ℝ)*X 2 1+(84199477/100000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_e011_c09_s0_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp28 : ((-3800901/25000000 : ℝ)*X 0 0+(775958079/2000000000 : ℝ)*X 0 1+(2982050509/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_e011_c09_s0_28 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp29 : ((93810719/125000000 : ℝ)*X 1 0+(-51167067/200000000 : ℝ)*X 1 1+(526636829/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_e011_c09_s0_29 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp30 : ((1500971277/2000000000 : ℝ)*X 2 0+(102155383/400000000 : ℝ)*X 2 1+(-132299389/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_e011_c09_s0_30 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp34 : ((2619519/10000000000 : ℝ)*X 0 0+(2578087961/10000000000 : ℝ)*X 0 1+(4079007847/5000000000 : ℝ)*X 0 2+(2619519/10000000000 : ℝ)*X 1 0+(2578087961/10000000000 : ℝ)*X 1 1+(4079007847/5000000000 : ℝ)*X 1 2+(2619519/10000000000 : ℝ)*X 2 0+(2578087961/10000000000 : ℝ)*X 2 1+(4079007847/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_e011_c09_s0_34 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp35 : ((-768174737/2000000000 : ℝ)*X 0 0+(4550805707/10000000000 : ℝ)*X 0 1+(3166674349/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_e011_c09_s0_35 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp36 : ((2816528637/10000000000 : ℝ)*X 1 0+(-24493207/62500000 : ℝ)*X 1 1+(600230801/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_e011_c09_s0_36 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp37 : ((7090486789/10000000000 : ℝ)*X 2 0+(3171574049/10000000000 : ℝ)*X 2 1+(-894343531/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_e011_c09_s0_37 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp41 : ((859/5000000000 : ℝ)*X 0 0+(4550805707/10000000000 : ℝ)*X 0 1+(799186673/1250000000 : ℝ)*X 0 2+(859/5000000000 : ℝ)*X 1 0+(4550805707/10000000000 : ℝ)*X 1 1+(799186673/1250000000 : ℝ)*X 1 2+(859/5000000000 : ℝ)*X 2 0+(4550805707/10000000000 : ℝ)*X 2 1+(799186673/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_e011_c09_s0_41 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp42 : ((-1429629757/10000000000 : ℝ)*X 0 0+(7275230259/10000000000 : ℝ)*X 0 1+(2491986251/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_e011_c09_s0_42 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp43 : ((7457245253/10000000000 : ℝ)*X 1 0+(-777032241/10000000000 : ℝ)*X 1 1+(284778313/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_e011_c09_s0_43 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp44 : ((3728624241/5000000000 : ℝ)*X 2 0+(709877643/5000000000 : ℝ)*X 2 1+(-1142321309/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_e011_c09_s0_44 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp48 : ((3007877/10000000000 : ℝ)*X 0 0+(1657643197/2500000000 : ℝ)*X 0 1+(4298351289/10000000000 : ℝ)*X 0 2+(3007877/10000000000 : ℝ)*X 1 0+(1657643197/2500000000 : ℝ)*X 1 1+(4298351289/10000000000 : ℝ)*X 1 2+(3007877/10000000000 : ℝ)*X 2 0+(1657643197/2500000000 : ℝ)*X 2 1+(4298351289/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_e011_c09_s0_48 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have r0 : (0 : ℝ) ≤ ((44391/100000 : ℝ)*X 1 0+(1 : ℝ)*X 1 1+(44391/100000 : ℝ)*X 2 0+(1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1392402496069876135431/5000000000000000000000 : ℝ) := by norm_num
    linear_combination (97582004893/500000000000 : ℝ)*(base1) + (1048644313947/1000000000000 : ℝ)*(base7) + (2339858001761/1000000000000 : ℝ)*(major0) + (2339858001761/1000000000000 : ℝ)*(major1) + (2339858001761/1000000000000 : ℝ)*(major2) + (94696354969/500000000000 : ℝ)*(sp0) + (19233986883/1000000000000 : ℝ)*(sp2) + (3282761038689/1000000000000 : ℝ)*(sp7) + (1437265974629/500000000000 : ℝ)*(sp8) + (1336232009821/500000000000 : ℝ)*(sp9) + (737243821227/500000000000 : ℝ)*(sp13) + (45945275043/250000000000 : ℝ)*(sp20) + (146322933079/250000000000 : ℝ)*(sp23) + (402457789583/1000000000000 : ℝ)*(sp36) + (160957687693/200000000000 : ℝ)*(f.failure) + (3276989738841/1000000000000 : ℝ)*(f.sum) + (248113003/10000000000000000000000 : ℝ)*base65 + (772848797/10000000000000000000000 : ℝ)*base68 + (1066335819/5000000000000000000000 : ℝ)*base69 + (410577333/2000000000000000000000 : ℝ)*base71 + (702440559/5000000000000000000000 : ℝ)*base73 + (425124857/1250000000000000000000 : ℝ)*base75 + (65222879/312500000000000000000 : ℝ)*base77 + (2130797551/10000000000000000000000 : ℝ)*base79 + (350631329/1000000000000000000000 : ℝ)*base81 + (9103/10000000000000000 : ℝ)*base89 + (9103/10000000000000000 : ℝ)*base91 + (9103/10000000000000000 : ℝ)*base93 + hcertificate_margin
  have out0 : |(X 1 1+X 2 1)| ≤ (44391/100000 : ℝ)*(X 1 0+X 2 0) := by
    rw [abs_of_nonpos sign0]
    linarith only [r0]
  have r1 : (0 : ℝ) ≤ ((44391/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 2+(44391/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (199963804877392089531/1250000000000000000000 : ℝ) := by norm_num
    linear_combination (199665750713/200000000000 : ℝ)*(base7) + (633140619/125000000000 : ℝ)*(base23) + (17637107643/200000000000 : ℝ)*(base34) + (801984577/500000000000 : ℝ)*(base43) + (17684881363/125000000000 : ℝ)*(base59) + (836930829329/500000000000 : ℝ)*(major0) + (1585676120443/1000000000000 : ℝ)*(major1) + (836930829329/500000000000 : ℝ)*(major2) + (818984046433/500000000000 : ℝ)*(sp14) + (447560803459/200000000000 : ℝ)*(sp15) + (127551320909/62500000000 : ℝ)*(sp16) + (787024689131/500000000000 : ℝ)*(sp20) + (1620815931/15625000000 : ℝ)*(sp23) + (255825193107/500000000000 : ℝ)*(sp42) + (287860312349/500000000000 : ℝ)*(f.failure) + (447560803459/200000000000 : ℝ)*(f.sum) + (807883807/1250000000000000000000 : ℝ)*base65 + (2272834507/5000000000000000000000 : ℝ)*base68 + (425995353/5000000000000000000000 : ℝ)*base70 + (407536593/5000000000000000000000 : ℝ)*base71 + (984177941/10000000000000000000000 : ℝ)*base73 + (1878161023/10000000000000000000000 : ℝ)*base76 + (224648967/625000000000000000000 : ℝ)*base78 + (1618558443/5000000000000000000000 : ℝ)*base80 + (47678519/100000000000000000000 : ℝ)*base81 + (36479/25000000000000000 : ℝ)*base89 + (36479/25000000000000000 : ℝ)*base91 + (36479/25000000000000000 : ℝ)*base93 + (1/1000000000000 : ℝ)*base96 + hcertificate_margin
  have out1 : |(X 1 2+X 2 2)| ≤ (44391/100000 : ℝ)*(X 1 0+X 2 0) := by
    rw [abs_of_nonneg sign1]
    linarith only [r1]
  have r2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(44391/100000 : ℝ)*X 0 1+(1 : ℝ)*X 2 0+(44391/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (36191494445877228591/400000000000000000000 : ℝ) := by norm_num
    linear_combination (447441876083/1000000000000 : ℝ)*(base1) + (815443177307/500000000000 : ℝ)*(base7) + (17362449957/1000000000000 : ℝ)*(base57) + (377974499/156250000 : ℝ)*(major0) + (377974499/156250000 : ℝ)*(major1) + (2401674343643/1000000000000 : ℝ)*(major2) + (97729821557/500000000000 : ℝ)*(sp9) + (4844107/3125000000 : ℝ)*(sp20) + (677712660919/200000000000 : ℝ)*(sp21) + (3149292715599/1000000000000 : ℝ)*(sp22) + (2977504785813/1000000000000 : ℝ)*(sp23) + (1996553704649/1000000000000 : ℝ)*(sp27) + (62301362593/250000000000 : ℝ)*(sp35) + (8206832657/200000000000 : ℝ)*(sp43) + (208005447579/250000000000 : ℝ)*(f.failure) + (797581719721/250000000000 : ℝ)*(f.sum) + (69650701/5000000000000000000000 : ℝ)*base65 + (1284515661/5000000000000000000000 : ℝ)*base67 + (8263269247/10000000000000000000000 : ℝ)*base69 + (463001593/10000000000000000000000 : ℝ)*base71 + (1883638813/10000000000000000000000 : ℝ)*base73 + (8421227749/10000000000000000000000 : ℝ)*base75 + (349201839/10000000000000000000000 : ℝ)*base78 + (982022859/5000000000000000000000 : ℝ)*base79 + (425498587/625000000000000000000 : ℝ)*base81 + (6809/12500000000000000 : ℝ)*base89 + (6809/12500000000000000 : ℝ)*base91 + (6809/12500000000000000 : ℝ)*base93 + (1/1000000000000 : ℝ)*base96 + hcertificate_margin
  have out2 : |(X 0 0+X 2 0)| ≤ (44391/100000 : ℝ)*(X 0 1+X 2 1) := by
    rw [abs_of_nonpos sign2]
    linarith only [r2]
  have r3 : (0 : ℝ) ≤ ((44391/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(44391/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (41711871682941009/5000000000000000000000 : ℝ) := by norm_num
    linear_combination (37674114127/250000000000 : ℝ)*(base1) + (729470323703/500000000000 : ℝ)*(base7) + (154345942463/100000000000 : ℝ)*(major0) + (154345942463/100000000000 : ℝ)*(major1) + (154345942463/100000000000 : ℝ)*(major2) + (2872137/1000000000000 : ℝ)*(sp22) + (37344749/1000000000000 : ℝ)*(sp27) + (1002000281381/500000000000 : ℝ)*(sp28) + (185329014077/100000000000 : ℝ)*(sp29) + (463324158183/250000000000 : ℝ)*(sp30) + (919537970651/500000000000 : ℝ)*(sp34) + (336017/1000000000000 : ℝ)*(sp35) + (2857341/250000000000 : ℝ)*(sp43) + (7809539/1000000000000 : ℝ)*(sp44) + (530869095153/1000000000000 : ℝ)*(f.failure) + (1853304442271/1000000000000 : ℝ)*(f.sum) + (777627279/10000000000000000000000 : ℝ)*base65 + (40344979/250000000000000000000 : ℝ)*base68 + (1964668537/10000000000000000000000 : ℝ)*base70 + (21658267/250000000000000000000 : ℝ)*base72 + (33735249/2500000000000000000000 : ℝ)*base74 + (191494551/10000000000000000000000 : ℝ)*base76 + (110287723/1250000000000000000000 : ℝ)*base78 + (122561041/2000000000000000000000 : ℝ)*base80 + (21468901/5000000000000000000000 : ℝ)*base82 + (13237/50000000000000000 : ℝ)*base90 + (13237/50000000000000000 : ℝ)*base92 + (13237/50000000000000000 : ℝ)*base94 + hcertificate_margin
  have out3 : |(X 0 2+X 2 2)| ≤ (44391/100000 : ℝ)*(X 0 1+X 2 1) := by
    rw [abs_of_nonneg sign3]
    linarith only [r3]
  have r4 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(44391/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(44391/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (2095702763637479536923/10000000000000000000000 : ℝ) := by norm_num
    linear_combination (1057594908511/1000000000000 : ℝ)*(base1) + (29110279543/20000000000 : ℝ)*(base7) + (1321110423/100000000000 : ℝ)*(base16) + (215238027939/500000000000 : ℝ)*(base43) + (506859586531/250000000000 : ℝ)*(major0) + (506859586531/250000000000 : ℝ)*(major1) + (506859586531/250000000000 : ℝ)*(major2) + (399080084949/1000000000000 : ℝ)*(sp8) + (31294576783/1000000000000 : ℝ)*(sp16) + (3644190407639/1000000000000 : ℝ)*(sp35) + (2174304309949/1000000000000 : ℝ)*(sp36) + (1277650461173/500000000000 : ℝ)*(sp37) + (189184198427/250000000000 : ℝ)*(sp41) + (42314342093/125000000000 : ℝ)*(sp48) + (697332461813/1000000000000 : ℝ)*(f.failure) + (2586595499129/1000000000000 : ℝ)*(f.sum) + (881854317/10000000000000000000000 : ℝ)*base66 + (58304001/10000000000000000000000 : ℝ)*base68 + (343662701/10000000000000000000000 : ℝ)*base69 + (53008877/625000000000000000000 : ℝ)*base72 + (1382692963/2500000000000000000000 : ℝ)*base74 + (375274059/5000000000000000000000 : ℝ)*base76 + (981414631/2000000000000000000000 : ℝ)*base78 + (5945444929/10000000000000000000000 : ℝ)*base80 + (964876627/5000000000000000000000 : ℝ)*base81 + (1/1000000000000 : ℝ)*base84 + (1/1000000000000 : ℝ)*base86 + (17623/50000000000000000 : ℝ)*base89 + (17623/50000000000000000 : ℝ)*base91 + (17623/50000000000000000 : ℝ)*base93 + hcertificate_margin
  have out4 : |(X 0 0+X 1 0)| ≤ (44391/100000 : ℝ)*(X 0 2+X 1 2) := by
    rw [abs_of_nonpos sign4]
    linarith only [r4]
  have r5 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 1+(44391/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 1+(44391/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (3005586688416985209/1000000000000000000000 : ℝ) := by norm_num
    linear_combination (271626640987/1000000000000 : ℝ)*(base1) + (1461012165121/1000000000000 : ℝ)*(base7) + (30874731/100000000000 : ℝ)*(base43) + (15748469667/10000000000 : ℝ)*(major0) + (15748469667/10000000000 : ℝ)*(major1) + (15748469667/10000000000 : ℝ)*(major2) + (591644919/200000000000 : ℝ)*(sp7) + (295397973/250000000000 : ℝ)*(sp9) + (3103559013/1000000000000 : ℝ)*(sp22) + (1303225819/125000000000 : ℝ)*(sp30) + (1085977692179/500000000000 : ℝ)*(sp42) + (1900183408953/1000000000000 : ℝ)*(sp43) + (1891679569523/1000000000000 : ℝ)*(sp44) + (1731050287637/1000000000000 : ℝ)*(sp48) + (270832381751/500000000000 : ℝ)*(f.failure) + (1903286967967/1000000000000 : ℝ)*(f.sum) + (1592397/2500000000000000000000 : ℝ)*base66 + (3018534943/10000000000000000000000 : ℝ)*base68 + (3942268541/10000000000000000000000 : ℝ)*base70 + (657417341/2500000000000000000000 : ℝ)*base71 + (222405809/2500000000000000000000 : ℝ)*base73 + (59245503/200000000000000000000 : ℝ)*base76 + (4153025047/10000000000000000000000 : ℝ)*base78 + (722720411/5000000000000000000000 : ℝ)*base80 + (1548309279/10000000000000000000000 : ℝ)*base82 + (1/1000000000000 : ℝ)*base84 + (1/1000000000000 : ℝ)*base86 + (24621/25000000000000000 : ℝ)*base89 + (24621/25000000000000000 : ℝ)*base91 + (24621/25000000000000000 : ℝ)*base93 + (1/1000000000000 : ℝ)*base95 + hcertificate_margin
  have out5 : |(X 0 1+X 1 1)| ≤ (44391/100000 : ℝ)*(X 0 2+X 1 2) := by
    rw [abs_of_nonneg sign5]
    linarith only [r5]
  intro i h hij
  fin_cases i <;> fin_cases h <;> try contradiction
  · change |pair X 0 1| ≤ (44391/100000 : ℝ)*pair X 0 0
    simpa only [pair0,pair1,pair2,Pi.add_apply] using out0
  · change |pair X 0 2| ≤ (44391/100000 : ℝ)*pair X 0 0
    simpa only [pair0,pair1,pair2,Pi.add_apply] using out1
  · change |pair X 1 0| ≤ (44391/100000 : ℝ)*pair X 1 1
    simpa only [pair0,pair1,pair2,Pi.add_apply] using out2
  · change |pair X 1 2| ≤ (44391/100000 : ℝ)*pair X 1 1
    simpa only [pair0,pair1,pair2,Pi.add_apply] using out3
  · change |pair X 2 0| ≤ (44391/100000 : ℝ)*pair X 2 2
    simpa only [pair0,pair1,pair2,Pi.add_apply] using out4
  · change |pair X 2 1| ≤ (44391/100000 : ℝ)*pair X 2 2
    simpa only [pair0,pair1,pair2,Pi.add_apply] using out5

end HlawkaSchatten.DiagonalCutoff6


open HlawkaSchatten HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem solution (p : ℝ) (hpa : (59/8 : ℝ) ≤ p) (hpb : p ≤ (15/2 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (145371/50000 : ℝ) (18063/12500 : ℝ) (43079/50000 : ℝ) X)
    (sign0 : (X 1 1+X 2 1) ≤ 0)
    (sign1 : 0 ≤ (X 1 2+X 2 2))
    (sign2 : (X 0 0+X 2 0) ≤ 0)
    (sign3 : 0 ≤ (X 0 2+X 2 2))
    (sign4 : (X 0 0+X 1 0) ≤ 0)
    (sign5 : 0 ≤ (X 0 1+X 1 1))
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1 : ℝ)*pair X i i) :
    ∀ i h, i ≠ h → |pair X i h| ≤ (44391/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff6.sign_e011_c09_s0 p hpa hpb X hX sign0 sign1 sign2 sign3 sign4 sign5 hratio

#print axioms solution
