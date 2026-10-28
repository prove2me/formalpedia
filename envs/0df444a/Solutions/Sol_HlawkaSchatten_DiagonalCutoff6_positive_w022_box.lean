-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff6.positive_w022_box
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-27T19:45:21.362409+00:00
-- url     : https://prove2.me/submissions/897bfea6-7136-4224-96b3-6bf057590aeb

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
theorem support_w022_box_0 (p : ℝ) (hpa : (203/32 : ℝ) ≤ p) (hpb : p ≤ (407/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-677075909/10000000000 : ℝ)*x 0 + (53826503/100000000 : ℝ)*x 1 + (2691324799/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (407/64 : ℝ)) 407 343 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(-677075909/10000000000 : ℝ), (53826503/100000000 : ℝ), (2691324799/5000000000 : ℝ)] ![(4096823444717/100000000000000 : ℝ), (47951591977987/100000000000000 : ℝ), (47951584557297/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_w022_box_1 (p : ℝ) (hpa : (203/32 : ℝ) ≤ p) (hpb : p ≤ (407/64 : ℝ)) (x : Fin 3 → ℝ) :
    (2592671717/5000000000 : ℝ)*x 0 + (-956808487/10000000000 : ℝ)*x 1 + (5382649971/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (407/64 : ℝ)) 407 343 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(2592671717/5000000000 : ℝ), (-956808487/10000000000 : ℝ), (5382649971/10000000000 : ℝ)] ![(11468277169873/25000000000000 : ℝ), (6175302813051/100000000000000 : ℝ), (47951588500199/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_w022_box_2 (p : ℝ) (hpa : (203/32 : ℝ) ≤ p) (hpb : p ≤ (407/64 : ℝ)) (x : Fin 3 → ℝ) :
    (5185343319/10000000000 : ℝ)*x 0 + (5382650101/10000000000 : ℝ)*x 1 + (-191361693/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (407/64 : ℝ)) 407 343 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(5185343319/10000000000 : ℝ), (5382650101/10000000000 : ℝ), (-191361693/2000000000 : ℝ)] ![(45873107472293/100000000000000 : ℝ), (47951589874401/100000000000000 : ℝ), (771912830571/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_w022_box_6 (p : ℝ) (hpa : (203/32 : ℝ) ≤ p) (hpb : p ≤ (407/64 : ℝ)) (x : Fin 3 → ℝ) :
    (111701927/250000000 : ℝ)*x 0 + (3704325939/10000000000 : ℝ)*x 1 + (3704325847/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (407/64 : ℝ)) 407 343 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(111701927/250000000 : ℝ), (3704325939/10000000000 : ℝ), (3704325847/10000000000 : ℝ)] ![(38444750555929/100000000000000 : ℝ), (15388812585149/50000000000000 : ℝ), (7694406065821/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_w022_box_7 (p : ℝ) (hpa : (203/32 : ℝ) ≤ p) (hpb : p ≤ (407/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-137490751/1000000000 : ℝ)*x 0 + (640771281/1250000000 : ℝ)*x 1 + (2563085301/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (407/64 : ℝ)) 407 343 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(-137490751/1000000000 : ℝ), (640771281/1250000000 : ℝ), (2563085301/5000000000 : ℝ)] ![(9494779056057/100000000000000 : ℝ), (2828288038093/6250000000000 : ℝ), (45252612317611/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_w022_box_8 (p : ℝ) (hpa : (203/32 : ℝ) ≤ p) (hpb : p ≤ (407/64 : ℝ)) (x : Fin 3 → ℝ) :
    (5353986517/10000000000 : ℝ)*x 0 + (-1076035839/10000000000 : ℝ)*x 1 + (2563084551/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (407/64 : ℝ)) 407 343 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(5353986517/10000000000 : ℝ), (-1076035839/10000000000 : ℝ), (2563084551/5000000000 : ℝ)] ![(47648744102149/100000000000000 : ℝ), (3549329640327/50000000000000 : ℝ), (1810103864209/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_w022_box_9 (p : ℝ) (hpa : (203/32 : ℝ) ≤ p) (hpb : p ≤ (407/64 : ℝ)) (x : Fin 3 → ℝ) :
    (66924823/125000000 : ℝ)*x 0 + (1281542439/2500000000 : ℝ)*x 1 + (-1076035877/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (407/64 : ℝ)) 407 343 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(66924823/125000000 : ℝ), (1281542439/2500000000 : ℝ), (-1076035877/10000000000 : ℝ)] ![(5956092119107/12500000000000 : ℝ), (1810104138233/4000000000000 : ℝ), (7098659578117/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_w022_box_13 (p : ℝ) (hpa : (203/32 : ℝ) ≤ p) (hpb : p ≤ (407/64 : ℝ)) (x : Fin 3 → ℝ) :
    (167832711/500000000 : ℝ)*x 0 + (4258016193/10000000000 : ℝ)*x 1 + (4258016239/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (407/64 : ℝ)) 407 343 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(167832711/500000000 : ℝ), (4258016193/10000000000 : ℝ), (4258016239/10000000000 : ℝ)] ![(6845198382311/25000000000000 : ℝ), (4538700374391/12500000000000 : ℝ), (36309603460577/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_w022_box_14 (p : ℝ) (hpa : (203/32 : ℝ) ≤ p) (hpb : p ≤ (407/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-611231379/5000000000 : ℝ)*x 0 + (1231702127/2500000000 : ℝ)*x 1 + (5441007893/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (407/64 : ℝ)) 407 343 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(-611231379/5000000000 : ℝ), (1231702127/2500000000 : ℝ), (5441007893/10000000000 : ℝ)] ![(8258932554477/100000000000000 : ℝ), (10792991965727/25000000000000 : ℝ), (24284549783201/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_w022_box_15 (p : ℝ) (hpa : (203/32 : ℝ) ≤ p) (hpb : p ≤ (407/64 : ℝ)) (x : Fin 3 → ℝ) :
    (5147069167/10000000000 : ℝ)*x 0 + (-928524001/10000000000 : ℝ)*x 1 + (2720503977/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (407/64 : ℝ)) 407 343 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(5147069167/10000000000 : ℝ), (-928524001/10000000000 : ℝ), (2720503977/5000000000 : ℝ)] ![(9094321274347/20000000000000 : ℝ), (5959293406027/100000000000000 : ℝ), (24284550106259/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_w022_box_16 (p : ℝ) (hpa : (203/32 : ℝ) ≤ p) (hpb : p ≤ (407/64 : ℝ)) (x : Fin 3 → ℝ) :
    (2573534579/5000000000 : ℝ)*x 0 + (1088201597/2000000000 : ℝ)*x 1 + (-92852397/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (407/64 : ℝ)) 407 343 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(2573534579/5000000000 : ℝ), (1088201597/2000000000 : ℝ), (-92852397/1000000000 : ℝ)] ![(45471606277389/100000000000000 : ℝ), (48569100540873/100000000000000 : ℝ), (744911646243/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_w022_box_20 (p : ℝ) (hpa : (203/32 : ℝ) ≤ p) (hpb : p ≤ (407/64 : ℝ)) (x : Fin 3 → ℝ) :
    (4710300761/10000000000 : ℝ)*x 0 + (894467807/2500000000 : ℝ)*x 1 + (1788935541/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (407/64 : ℝ)) 407 343 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(4710300761/10000000000 : ℝ), (894467807/2500000000 : ℝ), (1788935541/5000000000 : ℝ)] ![(20465065593501/50000000000000 : ℝ), (29534935113191/100000000000000 : ℝ), (29534933683097/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_w022_box_21 (p : ℝ) (hpa : (203/32 : ℝ) ≤ p) (hpb : p ≤ (407/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-32536577/400000000 : ℝ)*x 0 + (278574467/500000000 : ℝ)*x 1 + (5097513633/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (407/64 : ℝ)) 407 343 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(-32536577/400000000 : ℝ), (278574467/500000000 : ℝ), (5097513633/10000000000 : ℝ)] ![(5093169587383/100000000000000 : ℝ), (24977120431467/50000000000000 : ℝ), (22476294767687/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_w022_box_22 (p : ℝ) (hpa : (203/32 : ℝ) ≤ p) (hpb : p ≤ (407/64 : ℝ)) (x : Fin 3 → ℝ) :
    (5372910651/10000000000 : ℝ)*x 0 + (-544405609/5000000000 : ℝ)*x 1 + (127437797/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (407/64 : ℝ)) 407 343 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(5372910651/10000000000 : ℝ), (-544405609/5000000000 : ℝ), (127437797/250000000 : ℝ)] ![(1913946146059/4000000000000 : ℝ), (224961723411/3125000000000 : ℝ), (4495257119203/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_w022_box_23 (p : ℝ) (hpa : (203/32 : ℝ) ≤ p) (hpb : p ≤ (407/64 : ℝ)) (x : Fin 3 → ℝ) :
    (5372908259/10000000000 : ℝ)*x 0 + (1274378421/2500000000 : ℝ)*x 1 + (-1063293/9765625 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (407/64 : ℝ)) 407 343 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(5372908259/10000000000 : ℝ), (1274378421/2500000000 : ℝ), (-1063293/9765625 : ℝ)] ![(23924314187353/50000000000000 : ℝ), (11238147517259/25000000000000 : ℝ), (7198781535179/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_w022_box_27 (p : ℝ) (hpa : (203/32 : ℝ) ≤ p) (hpb : p ≤ (407/64 : ℝ)) (x : Fin 3 → ℝ) :
    (3227209581/10000000000 : ℝ)*x 0 + (4319621507/10000000000 : ℝ)*x 1 + (4319620307/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (407/64 : ℝ)) 407 343 (by norm_num)
    (by linarith) (by norm_num) hpb (by norm_num) ![(3227209581/10000000000 : ℝ), (4319621507/10000000000 : ℝ), (4319620307/10000000000 : ℝ)] ![(26132427954039/100000000000000 : ℝ), (36933792103969/100000000000000 : ℝ), (9233444982307/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_w022_box (p : ℝ) (hpa : (203/32 : ℝ) ≤ p) (hpb : p ≤ (407/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (61349/25000 : ℝ) (75087/50000 : ℝ) (84097/100000 : ℝ) X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17197/100000 : ℝ)*pair X i i) :
    -(69999/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(30087/50000 : ℝ) ∧ (10471/12500 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (2931/3125 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f (by norm_num)
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have ratio0 : (X 1 1+X 2 1) ≤ (17197/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have ratio1 : (X 1 2+X 2 2) ≤ (17197/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have ratio2 : (X 0 0+X 2 0) ≤ (17197/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have ratio3 : (X 0 2+X 2 2) ≤ (17197/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have ratio4 : (X 0 0+X 1 0) ≤ (17197/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have ratio5 : (X 0 1+X 1 1) ≤ (17197/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
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
  have base24 : ((-1 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 2).1]
  have base53 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [sign3]
  have base59 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*X 1 0) ≤ (0 : ℝ) := by
    linarith only [sign4]
  have base61 : ((-1 : ℝ)*X 0 1+(-1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [sign5]
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
  have hpow : (17197/100000 : ℝ) ^ (203/32 : ℝ) ≤ (11032985325769/781250000000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17197/100000 : ℝ)) (X := (11032985325769/781250000000000000 : ℝ)) (by norm_num) (by norm_num) 203 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hcorner1 : (781261032985325769/781250000000000000 : ℝ) ≤ (625001392957/625000000000 : ℝ) ^ (203/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (625001392957/625000000000 : ℝ)) (X := (781261032985325769/781250000000000000 : ℝ)) (by norm_num) 203 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hcorner2 : (390636032985325769/390625000000000000 : ℝ) ≤ (312501392957/312500000000 : ℝ) ^ (203/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (312501392957/312500000000 : ℝ)) (X := (390636032985325769/390625000000000000 : ℝ)) (by norm_num) 203 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have major0 : P 0 ≤ (X 1 0+X 2 0)+(81/6250000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := positive_pair_majorant (p := p) (a := (203/32 : ℝ)) (rho := (17197/100000 : ℝ)) (alpha := (81/6250000 : ℝ))
      (by linarith) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [hpow,hcorner1]) (by linarith only [hpow,hcorner2])
      X hmain hsign hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (X 0 1+X 2 1)+(81/6250000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := positive_pair_majorant (p := p) (a := (203/32 : ℝ)) (rho := (17197/100000 : ℝ)) (alpha := (81/6250000 : ℝ))
      (by linarith) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [hpow,hcorner1]) (by linarith only [hpow,hcorner2])
      X hmain hsign hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (X 0 2+X 1 2)+(81/6250000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := positive_pair_majorant (p := p) (a := (203/32 : ℝ)) (rho := (17197/100000 : ℝ)) (alpha := (81/6250000 : ℝ))
      (by linarith) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [hpow,hcorner1]) (by linarith only [hpow,hcorner2])
      X hmain hsign hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-677075909/10000000000 : ℝ)*X 0 0+(53826503/100000000 : ℝ)*X 0 1+(2691324799/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_w022_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2592671717/5000000000 : ℝ)*X 1 0+(-956808487/10000000000 : ℝ)*X 1 1+(5382649971/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_w022_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5185343319/10000000000 : ℝ)*X 2 0+(5382650101/10000000000 : ℝ)*X 2 1+(-191361693/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_w022_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((111701927/250000000 : ℝ)*X 0 0+(3704325939/10000000000 : ℝ)*X 0 1+(3704325847/10000000000 : ℝ)*X 0 2+(111701927/250000000 : ℝ)*X 1 0+(3704325939/10000000000 : ℝ)*X 1 1+(3704325847/10000000000 : ℝ)*X 1 2+(111701927/250000000 : ℝ)*X 2 0+(3704325939/10000000000 : ℝ)*X 2 1+(3704325847/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_w022_box_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((-137490751/1000000000 : ℝ)*X 0 0+(640771281/1250000000 : ℝ)*X 0 1+(2563085301/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_w022_box_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((5353986517/10000000000 : ℝ)*X 1 0+(-1076035839/10000000000 : ℝ)*X 1 1+(2563084551/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_w022_box_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((66924823/125000000 : ℝ)*X 2 0+(1281542439/2500000000 : ℝ)*X 2 1+(-1076035877/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_w022_box_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((167832711/500000000 : ℝ)*X 0 0+(4258016193/10000000000 : ℝ)*X 0 1+(4258016239/10000000000 : ℝ)*X 0 2+(167832711/500000000 : ℝ)*X 1 0+(4258016193/10000000000 : ℝ)*X 1 1+(4258016239/10000000000 : ℝ)*X 1 2+(167832711/500000000 : ℝ)*X 2 0+(4258016193/10000000000 : ℝ)*X 2 1+(4258016239/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_w022_box_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((-611231379/5000000000 : ℝ)*X 0 0+(1231702127/2500000000 : ℝ)*X 0 1+(5441007893/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_w022_box_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((5147069167/10000000000 : ℝ)*X 1 0+(-928524001/10000000000 : ℝ)*X 1 1+(2720503977/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_w022_box_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp16 : ((2573534579/5000000000 : ℝ)*X 2 0+(1088201597/2000000000 : ℝ)*X 2 1+(-92852397/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_w022_box_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp20 : ((4710300761/10000000000 : ℝ)*X 0 0+(894467807/2500000000 : ℝ)*X 0 1+(1788935541/5000000000 : ℝ)*X 0 2+(4710300761/10000000000 : ℝ)*X 1 0+(894467807/2500000000 : ℝ)*X 1 1+(1788935541/5000000000 : ℝ)*X 1 2+(4710300761/10000000000 : ℝ)*X 2 0+(894467807/2500000000 : ℝ)*X 2 1+(1788935541/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_w022_box_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp21 : ((-32536577/400000000 : ℝ)*X 0 0+(278574467/500000000 : ℝ)*X 0 1+(5097513633/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_w022_box_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp22 : ((5372910651/10000000000 : ℝ)*X 1 0+(-544405609/5000000000 : ℝ)*X 1 1+(127437797/250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_w022_box_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp23 : ((5372908259/10000000000 : ℝ)*X 2 0+(1274378421/2500000000 : ℝ)*X 2 1+(-1063293/9765625 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_w022_box_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp27 : ((3227209581/10000000000 : ℝ)*X 0 0+(4319621507/10000000000 : ℝ)*X 0 1+(4319620307/10000000000 : ℝ)*X 0 2+(3227209581/10000000000 : ℝ)*X 1 0+(4319621507/10000000000 : ℝ)*X 1 1+(4319620307/10000000000 : ℝ)*X 1 2+(3227209581/10000000000 : ℝ)*X 2 0+(4319621507/10000000000 : ℝ)*X 2 1+(4319620307/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_w022_box_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-69999/100000 : ℝ) ≤ (-6999649364965569334077/10000000000000000000000 : ℝ) := by norm_num
    linear_combination (56207/200000000000 : ℝ)*(base53) + (6043/12500000000 : ℝ)*(base59) + (449037/500000000000 : ℝ)*(base61) + (94208449223/8000000000 : ℝ)*(major0) + (94208449223/8000000000 : ℝ)*(major1) + (94208449223/8000000000 : ℝ)*(major2) + (96992871/1000000000000 : ℝ)*(sp1) + (49439651/1000000000000 : ℝ)*(sp2) + (1950927/250000000000 : ℝ)*(sp6) + (3797321835569/200000000000 : ℝ)*(sp7) + (18986539849669/1000000000000 : ℝ)*(sp8) + (2373323425361/125000000000 : ℝ)*(sp9) + (1199697326249/250000000000 : ℝ)*(sp13) + (5532939/200000000000 : ℝ)*(sp21) + (149962409647/31250000000 : ℝ)*(f.failure) + (949331842127/50000000000 : ℝ)*(f.sum) + (745350887/2000000000000000000000 : ℝ)*base66 + (48025889/100000000000000000000 : ℝ)*base68 + (934014069/2000000000000000000000 : ℝ)*base70 + (4949267647/10000000000000000000000 : ℝ)*base72 + (913949643/2500000000000000000000 : ℝ)*base74 + (1554154699/10000000000000000000000 : ℝ)*base76 + (4134656651/10000000000000000000000 : ℝ)*base77 + (3762807881/10000000000000000000000 : ℝ)*base79 + (4588612229/10000000000000000000000 : ℝ)*base82 + (1/1000000000000 : ℝ)*base88 + (837/3125000000000000 : ℝ)*base89 + (837/3125000000000000 : ℝ)*base91 + (837/3125000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (30087/50000 : ℝ) ≤ (1504421978131671823947/2500000000000000000000 : ℝ) := by norm_num
    linear_combination (230107/1000000000000 : ℝ)*(ratio0) + (460157/1000000000000 : ℝ)*(ratio3) + (39543/500000000000 : ℝ)*(ratio4) + (13289372106577/1000000000000 : ℝ)*(major0) + (13289372106577/1000000000000 : ℝ)*(major1) + (13289372106577/1000000000000 : ℝ)*(major2) + (10481327461703/500000000000 : ℝ)*(sp0) + (20962666148923/1000000000000 : ℝ)*(sp1) + (20962647164567/1000000000000 : ℝ)*(sp2) + (5415473662599/1000000000000 : ℝ)*(sp6) + (1627757/200000000000 : ℝ)*(sp8) + (27123141/1000000000000 : ℝ)*(sp9) + (6665759/1000000000000 : ℝ)*(sp13) + (9682151/500000000000 : ℝ)*(sp14) + (2707740164179/500000000000 : ℝ)*(f.failure) + (5240668571927/250000000000 : ℝ)*(f.sum) + (382473453/1000000000000000000000 : ℝ)*base66 + (1201696259/2500000000000000000000 : ℝ)*base67 + (463823993/2500000000000000000000 : ℝ)*base69 + (2599311873/10000000000000000000000 : ℝ)*base71 + (633438429/1250000000000000000000 : ℝ)*base74 + (4643970143/10000000000000000000000 : ℝ)*base75 + (5060993987/10000000000000000000000 : ℝ)*base77 + (1426693389/10000000000000000000000 : ℝ)*base79 + (2254404521/5000000000000000000000 : ℝ)*base82 + (4971/12500000000000000 : ℝ)*base89 + (4971/12500000000000000 : ℝ)*base91 + (4971/12500000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (10471/12500 : ℝ) ≤ (4188504357168150076767/5000000000000000000000 : ℝ) := by norm_num
    linear_combination (76617/1000000000000 : ℝ)*(base24) + (127989/1000000000000 : ℝ)*(base61) + (2027/500000000000 : ℝ)*(ratio4) + (6193720306079/500000000000 : ℝ)*(major0) + (6193720306079/500000000000 : ℝ)*(major1) + (6193720306079/500000000000 : ℝ)*(major2) + (56607/100000000000 : ℝ)*(sp0) + (2089423/100000000000 : ℝ)*(sp1) + (7365997/200000000000 : ℝ)*(sp2) + (383469/62500000000 : ℝ)*(sp6) + (9723853971631/500000000000 : ℝ)*(sp14) + (19447687615103/1000000000000 : ℝ)*(sp15) + (19447671602731/1000000000000 : ℝ)*(sp16) + (2523966477831/500000000000 : ℝ)*(sp20) + (2523969545583/500000000000 : ℝ)*(f.failure) + (19447708509333/1000000000000 : ℝ)*(f.sum) + (277172681/2500000000000000000000 : ℝ)*base65 + (1423993939/1250000000000000000000 : ℝ)*base67 + (3646915901/5000000000000000000000 : ℝ)*base69 + (4087354677/10000000000000000000000 : ℝ)*base71 + (4164739521/10000000000000000000000 : ℝ)*base73 + (468210509/2500000000000000000000 : ℝ)*base75 + (204775797/2000000000000000000000 : ℝ)*base77 + (131407511/1250000000000000000000 : ℝ)*base79 + (1773399477/10000000000000000000000 : ℝ)*base82 + (1/1000000000000 : ℝ)*base84 + (3533/12500000000000000 : ℝ)*base90 + (3533/12500000000000000 : ℝ)*base92 + (3533/12500000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-2931/3125 : ℝ) ≤ (-4689455902484731575681/5000000000000000000000 : ℝ) := by norm_num
    linear_combination (340707/100000000000 : ℝ)*(base59) + (516191/200000000000 : ℝ)*(ratio1) + (528711/1000000000000 : ℝ)*(ratio2) + (4197/8000000000 : ℝ)*(ratio3) + (2610433008943/200000000000 : ℝ)*(major0) + (2610433008943/200000000000 : ℝ)*(major1) + (2610433008943/200000000000 : ℝ)*(major2) + (2797027/200000000000 : ℝ)*(sp7) + (587025307/1000000000000 : ℝ)*(sp8) + (118792707/1000000000000 : ℝ)*(sp13) + (2109812913943/100000000000 : ℝ)*(sp21) + (10548778049629/500000000000 : ℝ)*(sp22) + (4219628624913/200000000000 : ℝ)*(sp23) + (5318698565651/1000000000000 : ℝ)*(sp27) + (2659408679179/500000000000 : ℝ)*(f.failure) + (4219628624913/200000000000 : ℝ)*(f.sum) + (806793829/10000000000000000000000 : ℝ)*base65 + (1245759047/2500000000000000000000 : ℝ)*base68 + (1040283029/1000000000000000000000 : ℝ)*base70 + (321880903/625000000000000000000 : ℝ)*base72 + (1373378691/10000000000000000000000 : ℝ)*base74 + (66153353/78125000000000000000 : ℝ)*base76 + (1183597053/5000000000000000000000 : ℝ)*base78 + (156785749/312500000000000000000 : ℝ)*base80 + (37104599/40000000000000000000 : ℝ)*base82 + (14971/12500000000000000 : ℝ)*base89 + (14971/12500000000000000 : ℝ)*base91 + (14971/12500000000000000 : ℝ)*base93 + hcertificate_margin
theorem positive_w022_box (p : ℝ) (hpa : (203/32 : ℝ) ≤ p) (hpb : p ≤ (407/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (61349/25000 : ℝ) (75087/50000 : ℝ) (84097/100000 : ℝ) X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17197/100000 : ℝ)*pair X i i) :
    ∀ j i, if j=i then -(69999/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(30087/50000 : ℝ) else (10471/12500 : ℝ) ≤ X j i ∧ X j i ≤ (2931/3125 : ℝ) := by
  exact frame_box_of_base (base_w022_box p hpa hpb) X hX hsign hratio

end HlawkaSchatten.DiagonalCutoff6


open HlawkaSchatten HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem solution (p : ℝ) (hpa : (203/32 : ℝ) ≤ p) (hpb : p ≤ (407/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (61349/25000 : ℝ) (75087/50000 : ℝ) (84097/100000 : ℝ) X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17197/100000 : ℝ)*pair X i i) :
    ∀ j i, if j=i then -(69999/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(30087/50000 : ℝ) else (10471/12500 : ℝ) ≤ X j i ∧ X j i ≤ (2931/3125 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff6.positive_w022_box p hpa hpb X hX hsign hratio

#print axioms solution
