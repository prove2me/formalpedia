-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1186_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:51:26.960832+00:00
-- url     : https://prove2.me/submissions/b958d4cd-471f-462f-bd84-f239a0b24b91

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
theorem support_rectangle_w1186_s3_0 (p : ℝ) (hpa : (4189/1024 : ℝ) ≤ p) (hpb : p ≤ (8379/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2142672403/10000000000 : ℝ)*x 0 + (2712398629/5000000000 : ℝ)*x 1 + (5236052157/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2142672403/10000000000 : ℝ)^8379 ≤ (13017520350847/100000000000000 : ℝ)^6331 := by
    have hnat : (2142672403 : ℕ)^8379*100000000000000^6331 ≤ 13017520350847^6331*10000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2142672403 10000000000 13017520350847 100000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2712398629/5000000000 : ℝ)^8379 ≤ (44510233377553/100000000000000 : ℝ)^6331 := by
    have hnat : (2712398629 : ℕ)^8379*100000000000000^6331 ≤ 44510233377553^6331*5000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2712398629 5000000000 44510233377553 100000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5236052157/10000000000 : ℝ)^8379 ≤ (21236123131081/50000000000000 : ℝ)^6331 := by
    have hnat : (5236052157 : ℕ)^8379*50000000000000^6331 ≤ 21236123131081^6331*10000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5236052157 10000000000 21236123131081 50000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8379/2048 : ℝ)) 8379 6331 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2142672403/10000000000 : ℝ), (2712398629/5000000000 : ℝ), (5236052157/10000000000 : ℝ)] ![(13017520350847/100000000000000 : ℝ), (44510233377553/100000000000000 : ℝ), (21236123131081/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2142672403/10000000000 : ℝ)|^8379 ≤ (13017520350847/100000000000000 : ℝ)^6331
        have hw : |(-2142672403/10000000000 : ℝ)|=(2142672403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2712398629/5000000000 : ℝ)|^8379 ≤ (44510233377553/100000000000000 : ℝ)^6331
        have hw : |(2712398629/5000000000 : ℝ)|=(2712398629/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5236052157/10000000000 : ℝ)|^8379 ≤ (21236123131081/50000000000000 : ℝ)^6331
        have hw : |(5236052157/10000000000 : ℝ)|=(5236052157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1186_s3_1 (p : ℝ) (hpa : (4189/1024 : ℝ) ≤ p) (hpb : p ≤ (8379/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (669094433/1250000000 : ℝ)*x 0 + (-2239062661/10000000000 : ℝ)*x 1 + (1047210473/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (669094433/1250000000 : ℝ)^8379 ≤ (10932401362469/25000000000000 : ℝ)^6331 := by
    have hnat : (669094433 : ℕ)^8379*25000000000000^6331 ≤ 10932401362469^6331*1250000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      669094433 1250000000 10932401362469 25000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2239062661/10000000000 : ℝ)^8379 ≤ (6899073024119/50000000000000 : ℝ)^6331 := by
    have hnat : (2239062661 : ℕ)^8379*50000000000000^6331 ≤ 6899073024119^6331*10000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2239062661 10000000000 6899073024119 50000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1047210473/2000000000 : ℝ)^8379 ≤ (2123612424757/5000000000000 : ℝ)^6331 := by
    have hnat : (1047210473 : ℕ)^8379*5000000000000^6331 ≤ 2123612424757^6331*2000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1047210473 2000000000 2123612424757 5000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8379/2048 : ℝ)) 8379 6331 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(669094433/1250000000 : ℝ), (-2239062661/10000000000 : ℝ), (1047210473/2000000000 : ℝ)] ![(10932401362469/25000000000000 : ℝ), (6899073024119/50000000000000 : ℝ), (2123612424757/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(669094433/1250000000 : ℝ)|^8379 ≤ (10932401362469/25000000000000 : ℝ)^6331
        have hw : |(669094433/1250000000 : ℝ)|=(669094433/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2239062661/10000000000 : ℝ)|^8379 ≤ (6899073024119/50000000000000 : ℝ)^6331
        have hw : |(-2239062661/10000000000 : ℝ)|=(2239062661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1047210473/2000000000 : ℝ)|^8379 ≤ (2123612424757/5000000000000 : ℝ)^6331
        have hw : |(1047210473/2000000000 : ℝ)|=(1047210473/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1186_s3_2 (p : ℝ) (hpa : (4189/1024 : ℝ) ≤ p) (hpb : p ≤ (8379/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1070551071/2000000000 : ℝ)*x 0 + (5236052559/10000000000 : ℝ)*x 1 + (-2239062549/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1070551071/2000000000 : ℝ)^8379 ≤ (8745920854267/20000000000000 : ℝ)^6331 := by
    have hnat : (1070551071 : ℕ)^8379*20000000000000^6331 ≤ 8745920854267^6331*2000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070551071 2000000000 8745920854267 20000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5236052559/10000000000 : ℝ)^8379 ≤ (42472250577821/100000000000000 : ℝ)^6331 := by
    have hnat : (5236052559 : ℕ)^8379*100000000000000^6331 ≤ 42472250577821^6331*10000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5236052559 10000000000 42472250577821 100000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2239062549/10000000000 : ℝ)^8379 ≤ (3449536283693/25000000000000 : ℝ)^6331 := by
    have hnat : (2239062549 : ℕ)^8379*25000000000000^6331 ≤ 3449536283693^6331*10000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2239062549 10000000000 3449536283693 25000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8379/2048 : ℝ)) 8379 6331 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1070551071/2000000000 : ℝ), (5236052559/10000000000 : ℝ), (-2239062549/10000000000 : ℝ)] ![(8745920854267/20000000000000 : ℝ), (42472250577821/100000000000000 : ℝ), (3449536283693/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1070551071/2000000000 : ℝ)|^8379 ≤ (8745920854267/20000000000000 : ℝ)^6331
        have hw : |(1070551071/2000000000 : ℝ)|=(1070551071/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5236052559/10000000000 : ℝ)|^8379 ≤ (42472250577821/100000000000000 : ℝ)^6331
        have hw : |(5236052559/10000000000 : ℝ)|=(5236052559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2239062549/10000000000 : ℝ)|^8379 ≤ (3449536283693/25000000000000 : ℝ)^6331
        have hw : |(-2239062549/10000000000 : ℝ)|=(2239062549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1186_s3_3 (p : ℝ) (hpa : (4189/1024 : ℝ) ≤ p) (hpb : p ≤ (8379/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4356518911/10000000000 : ℝ)*x 0 + (4171194817/10000000000 : ℝ)*x 1 + (4549941251/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4356518911/10000000000 : ℝ)^8379 ≤ (16648524290497/50000000000000 : ℝ)^6331 := by
    have hnat : (4356518911 : ℕ)^8379*50000000000000^6331 ≤ 16648524290497^6331*10000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4356518911 10000000000 16648524290497 50000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4171194817/10000000000 : ℝ)^8379 ≤ (15717716473693/50000000000000 : ℝ)^6331 := by
    have hnat : (4171194817 : ℕ)^8379*50000000000000^6331 ≤ 15717716473693^6331*10000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4171194817 10000000000 15717716473693 50000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4549941251/10000000000 : ℝ)^8379 ≤ (881687961469/2500000000000 : ℝ)^6331 := by
    have hnat : (4549941251 : ℕ)^8379*2500000000000^6331 ≤ 881687961469^6331*10000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4549941251 10000000000 881687961469 2500000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8379/2048 : ℝ)) 8379 6331 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4356518911/10000000000 : ℝ), (4171194817/10000000000 : ℝ), (4549941251/10000000000 : ℝ)] ![(16648524290497/50000000000000 : ℝ), (15717716473693/50000000000000 : ℝ), (881687961469/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4356518911/10000000000 : ℝ)|^8379 ≤ (16648524290497/50000000000000 : ℝ)^6331
        have hw : |(4356518911/10000000000 : ℝ)|=(4356518911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4171194817/10000000000 : ℝ)|^8379 ≤ (15717716473693/50000000000000 : ℝ)^6331
        have hw : |(4171194817/10000000000 : ℝ)|=(4171194817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4549941251/10000000000 : ℝ)|^8379 ≤ (881687961469/2500000000000 : ℝ)^6331
        have hw : |(4549941251/10000000000 : ℝ)|=(4549941251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1186_s3_4 (p : ℝ) (hpa : (4189/1024 : ℝ) ≤ p) (hpb : p ≤ (8379/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1071344307/5000000000 : ℝ)*x 0 + (1309190803/2500000000 : ℝ)*x 1 + (5424082267/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1071344307/5000000000 : ℝ)^8379 ≤ (13017650698347/100000000000000 : ℝ)^6331 := by
    have hnat : (1071344307 : ℕ)^8379*100000000000000^6331 ≤ 13017650698347^6331*5000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1071344307 5000000000 13017650698347 100000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1309190803/2500000000 : ℝ)^8379 ≤ (8495975988173/20000000000000 : ℝ)^6331 := by
    have hnat : (1309190803 : ℕ)^8379*20000000000000^6331 ≤ 8495975988173^6331*2500000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1309190803 2500000000 8495975988173 20000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5424082267/10000000000 : ℝ)^8379 ≤ (44502469341329/100000000000000 : ℝ)^6331 := by
    have hnat : (5424082267 : ℕ)^8379*100000000000000^6331 ≤ 44502469341329^6331*10000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5424082267 10000000000 44502469341329 100000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8379/2048 : ℝ)) 8379 6331 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1071344307/5000000000 : ℝ), (1309190803/2500000000 : ℝ), (5424082267/10000000000 : ℝ)] ![(13017650698347/100000000000000 : ℝ), (8495975988173/20000000000000 : ℝ), (44502469341329/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1071344307/5000000000 : ℝ)|^8379 ≤ (13017650698347/100000000000000 : ℝ)^6331
        have hw : |(-1071344307/5000000000 : ℝ)|=(1071344307/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1309190803/2500000000 : ℝ)|^8379 ≤ (8495975988173/20000000000000 : ℝ)^6331
        have hw : |(1309190803/2500000000 : ℝ)|=(1309190803/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5424082267/10000000000 : ℝ)|^8379 ≤ (44502469341329/100000000000000 : ℝ)^6331
        have hw : |(5424082267/10000000000 : ℝ)|=(5424082267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1186_s3_5 (p : ℝ) (hpa : (4189/1024 : ℝ) ≤ p) (hpb : p ≤ (8379/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1326196789/2500000000 : ℝ)*x 0 + (-1025516187/5000000000 : ℝ)*x 1 + (542408221/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1326196789/2500000000 : ℝ)^8379 ≤ (43211711059973/100000000000000 : ℝ)^6331 := by
    have hnat : (1326196789 : ℕ)^8379*100000000000000^6331 ≤ 43211711059973^6331*2500000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1326196789 2500000000 43211711059973 100000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1025516187/5000000000 : ℝ)^8379 ≤ (12285820200093/100000000000000 : ℝ)^6331 := by
    have hnat : (1025516187 : ℕ)^8379*100000000000000^6331 ≤ 12285820200093^6331*5000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1025516187 5000000000 12285820200093 100000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (542408221/1000000000 : ℝ)^8379 ≤ (2781404295149/6250000000000 : ℝ)^6331 := by
    have hnat : (542408221 : ℕ)^8379*6250000000000^6331 ≤ 2781404295149^6331*1000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      542408221 1000000000 2781404295149 6250000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8379/2048 : ℝ)) 8379 6331 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1326196789/2500000000 : ℝ), (-1025516187/5000000000 : ℝ), (542408221/1000000000 : ℝ)] ![(43211711059973/100000000000000 : ℝ), (12285820200093/100000000000000 : ℝ), (2781404295149/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1326196789/2500000000 : ℝ)|^8379 ≤ (43211711059973/100000000000000 : ℝ)^6331
        have hw : |(1326196789/2500000000 : ℝ)|=(1326196789/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1025516187/5000000000 : ℝ)|^8379 ≤ (12285820200093/100000000000000 : ℝ)^6331
        have hw : |(-1025516187/5000000000 : ℝ)|=(1025516187/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(542408221/1000000000 : ℝ)|^8379 ≤ (2781404295149/6250000000000 : ℝ)^6331
        have hw : |(542408221/1000000000 : ℝ)|=(542408221/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1186_s3_6 (p : ℝ) (hpa : (4189/1024 : ℝ) ≤ p) (hpb : p ≤ (8379/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (663098351/1250000000 : ℝ)*x 0 + (5424082591/10000000000 : ℝ)*x 1 + (-1025516163/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (663098351/1250000000 : ℝ)^8379 ≤ (21605853654117/50000000000000 : ℝ)^6331 := by
    have hnat : (663098351 : ℕ)^8379*50000000000000^6331 ≤ 21605853654117^6331*1250000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      663098351 1250000000 21605853654117 50000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5424082591/10000000000 : ℝ)^8379 ≤ (44502472859547/100000000000000 : ℝ)^6331 := by
    have hnat : (5424082591 : ℕ)^8379*100000000000000^6331 ≤ 44502472859547^6331*10000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5424082591 10000000000 44502472859547 100000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1025516163/5000000000 : ℝ)^8379 ≤ (307145495489/2500000000000 : ℝ)^6331 := by
    have hnat : (1025516163 : ℕ)^8379*2500000000000^6331 ≤ 307145495489^6331*5000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1025516163 5000000000 307145495489 2500000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8379/2048 : ℝ)) 8379 6331 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(663098351/1250000000 : ℝ), (5424082591/10000000000 : ℝ), (-1025516163/5000000000 : ℝ)] ![(21605853654117/50000000000000 : ℝ), (44502472859547/100000000000000 : ℝ), (307145495489/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(663098351/1250000000 : ℝ)|^8379 ≤ (21605853654117/50000000000000 : ℝ)^6331
        have hw : |(663098351/1250000000 : ℝ)|=(663098351/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5424082591/10000000000 : ℝ)|^8379 ≤ (44502472859547/100000000000000 : ℝ)^6331
        have hw : |(5424082591/10000000000 : ℝ)|=(5424082591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1025516163/5000000000 : ℝ)|^8379 ≤ (307145495489/2500000000000 : ℝ)^6331
        have hw : |(-1025516163/5000000000 : ℝ)|=(1025516163/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1186_s3_7 (p : ℝ) (hpa : (4189/1024 : ℝ) ≤ p) (hpb : p ≤ (8379/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (174262067/400000000 : ℝ)*x 0 + (1137128539/2500000000 : ℝ)*x 1 + (4172629221/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (174262067/400000000 : ℝ)^8379 ≤ (4162172500577/12500000000000 : ℝ)^6331 := by
    have hnat : (174262067 : ℕ)^8379*12500000000000^6331 ≤ 4162172500577^6331*400000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      174262067 400000000 4162172500577 12500000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1137128539/2500000000 : ℝ)^8379 ≤ (35252879174619/100000000000000 : ℝ)^6331 := by
    have hnat : (1137128539 : ℕ)^8379*100000000000000^6331 ≤ 35252879174619^6331*2500000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1137128539 2500000000 35252879174619 100000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4172629221/10000000000 : ℝ)^8379 ≤ (31449740801053/100000000000000 : ℝ)^6331 := by
    have hnat : (4172629221 : ℕ)^8379*100000000000000^6331 ≤ 31449740801053^6331*10000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4172629221 10000000000 31449740801053 100000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8379/2048 : ℝ)) 8379 6331 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(174262067/400000000 : ℝ), (1137128539/2500000000 : ℝ), (4172629221/10000000000 : ℝ)] ![(4162172500577/12500000000000 : ℝ), (35252879174619/100000000000000 : ℝ), (31449740801053/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(174262067/400000000 : ℝ)|^8379 ≤ (4162172500577/12500000000000 : ℝ)^6331
        have hw : |(174262067/400000000 : ℝ)|=(174262067/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1137128539/2500000000 : ℝ)|^8379 ≤ (35252879174619/100000000000000 : ℝ)^6331
        have hw : |(1137128539/2500000000 : ℝ)|=(1137128539/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4172629221/10000000000 : ℝ)|^8379 ≤ (31449740801053/100000000000000 : ℝ)^6331
        have hw : |(4172629221/10000000000 : ℝ)|=(4172629221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1186_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4189/1024 : ℝ) ≤ p) (hpb : p ≤ (8379/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150332923/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (131/800 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1853/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (5381/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3689/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (131/800 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1853/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (131/800 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1853/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (131/800 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1853/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (131/800 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1853/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (131/800 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1853/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (131/800 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1853/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1853/20000 : ℝ) ^ (4189/1024 : ℝ) ≤ (5936770671857723/100000000000000000000 : ℝ) := by
    have hpowers : (1853/20000 : ℝ)^4189 ≤ (5936770671857723/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1853 : ℕ)^4189*100000000000000000000^1024 ≤ 5936770671857723^1024*20000^4189 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1853 20000 5936770671857723 100000000000000000000 4189 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1853/20000 : ℝ)) (X := (5936770671857723/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4189 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (131/800 : ℝ) ^ (4189/1024 : ℝ) ≤ (61003806596489553/100000000000000000000 : ℝ) := by
    have hpowers : (131/800 : ℝ)^4189 ≤ (61003806596489553/100000000000000000000 : ℝ)^1024 := by
      have hnat : (131 : ℕ)^4189*100000000000000000000^1024 ≤ 61003806596489553^1024*800^4189 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        131 800 61003806596489553 100000000000000000000 4189 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (131/800 : ℝ)) (X := (61003806596489553/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4189 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005936770671857723/50000000000000000000 : ℝ) ≤ (5000145117701129/5000000000000000 : ℝ) ^ (4189/1024 : ℝ) := by
    have hpowers : (50005936770671857723/50000000000000000000 : ℝ)^1024 ≤ (5000145117701129/5000000000000000 : ℝ)^4189 := by
      have hnat : (50005936770671857723 : ℕ)^1024*5000000000000000^4189 ≤ 5000145117701129^4189*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005936770671857723 50000000000000000000 5000145117701129 5000000000000000 1024 4189 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000145117701129/5000000000000000 : ℝ)) (X := (50005936770671857723/50000000000000000000 : ℝ)) (by norm_num) 4189 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25016735144317086819/25000000000000000000 : ℝ) ≤ (2500408986771151/2500000000000000 : ℝ) ^ (4189/1024 : ℝ) := by
    have hpowers : (25016735144317086819/25000000000000000000 : ℝ)^1024 ≤ (2500408986771151/2500000000000000 : ℝ)^4189 := by
      have hnat : (25016735144317086819 : ℕ)^1024*2500000000000000^4189 ≤ 2500408986771151^4189*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25016735144317086819 25000000000000000000 2500408986771151 2500000000000000 1024 4189 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500408986771151/2500000000000000 : ℝ)) (X := (25016735144317086819/25000000000000000000 : ℝ)) (by norm_num) 4189 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50061003806596489553/50000000000000000000 : ℝ) ≤ (200059633175339/200000000000000 : ℝ) ^ (4189/1024 : ℝ) := by
    have hpowers : (50061003806596489553/50000000000000000000 : ℝ)^1024 ≤ (200059633175339/200000000000000 : ℝ)^4189 := by
      have hnat : (50061003806596489553 : ℕ)^1024*200000000000000^4189 ≤ 200059633175339^4189*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50061003806596489553 50000000000000000000 200059633175339 200000000000000 1024 4189 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (200059633175339/200000000000000 : ℝ)) (X := (50061003806596489553/50000000000000000000 : ℝ)) (by norm_num) 4189 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5936770671857723/100000000000000000000 : ℝ) ≤ ((23692375845412061/23700000000000000 : ℝ)+2*(224285280391/118500000000000 : ℝ)*(1853/20000 : ℝ))^(4189/1024 : ℝ) := by
    rw [show (23692375845412061/23700000000000000 : ℝ)+2*(224285280391/118500000000000 : ℝ)*(1853/20000 : ℝ)=(5000145117701129/5000000000000000 : ℝ) by norm_num, show 1+2*(5936770671857723/100000000000000000000 : ℝ)=(50005936770671857723/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(61003806596489553/100000000000000000000 : ℝ)+(5936770671857723/100000000000000000000 : ℝ) ≤ ((23692375845412061/23700000000000000 : ℝ)+(224285280391/118500000000000 : ℝ)*((131/800 : ℝ)+(1853/20000 : ℝ)))^(4189/1024 : ℝ) := by
    rw [show (23692375845412061/23700000000000000 : ℝ)+(224285280391/118500000000000 : ℝ)*((131/800 : ℝ)+(1853/20000 : ℝ))=(2500408986771151/2500000000000000 : ℝ) by norm_num, show 1+(61003806596489553/100000000000000000000 : ℝ)+(5936770671857723/100000000000000000000 : ℝ)=(25016735144317086819/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(61003806596489553/100000000000000000000 : ℝ) ≤ ((23692375845412061/23700000000000000 : ℝ)+2*(224285280391/118500000000000 : ℝ)*(131/800 : ℝ))^(4189/1024 : ℝ) := by
    rw [show (23692375845412061/23700000000000000 : ℝ)+2*(224285280391/118500000000000 : ℝ)*(131/800 : ℝ)=(200059633175339/200000000000000 : ℝ) by norm_num, show 1+2*(61003806596489553/100000000000000000000 : ℝ)=(50061003806596489553/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (23692375845412061/23700000000000000 : ℝ)*(X 1 0+X 2 0)+(224285280391/118500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4189/1024 : ℝ)) (lo := (1853/20000 : ℝ)) (hi := (131/800 : ℝ)) (c := (23692375845412061/23700000000000000 : ℝ)) (alpha := (224285280391/118500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (23692375845412061/23700000000000000 : ℝ)*(X 0 1+X 2 1)+(224285280391/118500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4189/1024 : ℝ)) (lo := (1853/20000 : ℝ)) (hi := (131/800 : ℝ)) (c := (23692375845412061/23700000000000000 : ℝ)) (alpha := (224285280391/118500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (23692375845412061/23700000000000000 : ℝ)*(X 0 2+X 1 2)+(224285280391/118500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4189/1024 : ℝ)) (lo := (1853/20000 : ℝ)) (hi := (131/800 : ℝ)) (c := (23692375845412061/23700000000000000 : ℝ)) (alpha := (224285280391/118500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2142672403/10000000000 : ℝ)*X 0 0+(2712398629/5000000000 : ℝ)*X 0 1+(5236052157/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1186_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((669094433/1250000000 : ℝ)*X 1 0+(-2239062661/10000000000 : ℝ)*X 1 1+(1047210473/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1186_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1070551071/2000000000 : ℝ)*X 2 0+(5236052559/10000000000 : ℝ)*X 2 1+(-2239062549/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1186_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4356518911/10000000000 : ℝ)*X 0 0+(4171194817/10000000000 : ℝ)*X 0 1+(4549941251/10000000000 : ℝ)*X 0 2+(4356518911/10000000000 : ℝ)*X 1 0+(4171194817/10000000000 : ℝ)*X 1 1+(4549941251/10000000000 : ℝ)*X 1 2+(4356518911/10000000000 : ℝ)*X 2 0+(4171194817/10000000000 : ℝ)*X 2 1+(4549941251/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1186_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1071344307/5000000000 : ℝ)*X 0 0+(1309190803/2500000000 : ℝ)*X 0 1+(5424082267/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1186_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1326196789/2500000000 : ℝ)*X 1 0+(-1025516187/5000000000 : ℝ)*X 1 1+(542408221/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1186_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((663098351/1250000000 : ℝ)*X 2 0+(5424082591/10000000000 : ℝ)*X 2 1+(-1025516163/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1186_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((174262067/400000000 : ℝ)*X 0 0+(1137128539/2500000000 : ℝ)*X 0 1+(4172629221/10000000000 : ℝ)*X 0 2+(174262067/400000000 : ℝ)*X 1 0+(1137128539/2500000000 : ℝ)*X 1 1+(4172629221/10000000000 : ℝ)*X 1 2+(174262067/400000000 : ℝ)*X 2 0+(1137128539/2500000000 : ℝ)*X 2 1+(4172629221/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1186_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (612793997910836734651753/197500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2066033/1000000000000 : ℝ)*(base19) + (8984281/100000000000000 : ℝ)*(base23) + (12007641/25000000000000 : ℝ)*(lower2) + (2628591/100000000000000 : ℝ)*(upper3) + (9082041/25000000000000 : ℝ)*(upper5) + (1984616723162809/50000000000000 : ℝ)*(major0) + (1984616723162809/50000000000000 : ℝ)*(major1) + (1984616723162809/50000000000000 : ℝ)*(major2) + (2649080151738151/50000000000000 : ℝ)*(sp0) + (5298171052464273/100000000000000 : ℝ)*(sp1) + (5298171250083291/100000000000000 : ℝ)*(sp2) + (1320146220834041/50000000000000 : ℝ)*(sp3) + (10955591271/100000000000000 : ℝ)*(sp4) + (193030651/6250000000000 : ℝ)*(sp7) + (1320147765079249/50000000000000 : ℝ)*(f.failure) + (5298171259067573/100000000000000 : ℝ)*(f.sum) + (15379164549947/1481250000000000000000000000 : ℝ)*base65 + (7175297655173149/1185000000000000000000000000000 : ℝ)*base67 + (7119354953438149/1185000000000000000000000000000 : ℝ)*base69 + (197281869713149/1185000000000000000000000000000 : ℝ)*base71 + (30627938442413/5925000000000000000000000000 : ℝ)*base73 + (27853204117748149/1185000000000000000000000000000 : ℝ)*base75 + (33222360144608149/1185000000000000000000000000000 : ℝ)*base77 + (18829785333488149/1185000000000000000000000000000 : ℝ)*base79 + (1988465615437/5925000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (71185173/5000000000000000000000 : ℝ)*base90 + (71185173/5000000000000000000000 : ℝ)*base92 + (71185173/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (137146873574182492417113/24687500000000000000000000000 : ℝ) := by norm_num
    linear_combination (169876939/10000000000000 : ℝ)*(base19) + (1606052039/100000000000000 : ℝ)*(base23) + (107626537/100000000000000 : ℝ)*(upper3) + (25604217/20000000000000 : ℝ)*(lower4) + (213466059/100000000000000 : ℝ)*(upper5) + (999858662233541/25000000000000 : ℝ)*(major0) + (999858662233541/25000000000000 : ℝ)*(major1) + (999858662233541/25000000000000 : ℝ)*(major2) + (1062475967/3125000000000 : ℝ)*(sp1) + (8946595819/25000000000000 : ℝ)*(sp2) + (1067696807188209/20000000000000 : ℝ)*(sp4) + (5338448337940711/100000000000000 : ℝ)*(sp5) + (533844664350573/10000000000000 : ℝ)*(sp6) + (166274067296879/6250000000000 : ℝ)*(sp7) + (166274067296879/6250000000000 : ℝ)*(f.failure) + (1067696807188209/20000000000000 : ℝ)*(f.sum) + (11911337712937/2962500000000000000000000000 : ℝ)*base65 + (9581078476425799/592500000000000000000000000000 : ℝ)*base68 + (5282329007663299/592500000000000000000000000000 : ℝ)*base70 + (619220086665799/592500000000000000000000000000 : ℝ)*base72 + (7706511809287/2962500000000000000000000000 : ℝ)*base73 + (1685302215749201/592500000000000000000000000000 : ℝ)*base75 + (2735432717805799/592500000000000000000000000000 : ℝ)*base78 + (5255540032020799/592500000000000000000000000000 : ℝ)*base80 + (3129527759719/1481250000000000000000000000 : ℝ)*base82 + (3847317/625000000000000000000 : ℝ)*base89 + (3847317/625000000000000000000 : ℝ)*base91 + (3847317/625000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1186_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4189/1024 : ℝ) ≤ p) (hpb : p ≤ (8379/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150332923/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (131/800 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1853/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5381/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3689/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1186_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1186_s4_0 (p : ℝ) (hpa : (4189/1024 : ℝ) ≤ p) (hpb : p ≤ (8379/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-429067777/2000000000 : ℝ)*x 0 + (2699930571/5000000000 : ℝ)*x 1 + (1051848531/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (429067777/2000000000 : ℝ)^8379 ≤ (13038964973367/100000000000000 : ℝ)^6331 := by
    have hnat : (429067777 : ℕ)^8379*100000000000000^6331 ≤ 13038964973367^6331*2000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      429067777 2000000000 13038964973367 100000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2699930571/5000000000 : ℝ)^8379 ≤ (11059912408913/25000000000000 : ℝ)^6331 := by
    have hnat : (2699930571 : ℕ)^8379*25000000000000^6331 ≤ 11059912408913^6331*5000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2699930571 5000000000 11059912408913 25000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1051848531/2000000000 : ℝ)^8379 ≤ (21360692686439/50000000000000 : ℝ)^6331 := by
    have hnat : (1051848531 : ℕ)^8379*50000000000000^6331 ≤ 21360692686439^6331*2000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1051848531 2000000000 21360692686439 50000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8379/2048 : ℝ)) 8379 6331 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-429067777/2000000000 : ℝ), (2699930571/5000000000 : ℝ), (1051848531/2000000000 : ℝ)] ![(13038964973367/100000000000000 : ℝ), (11059912408913/25000000000000 : ℝ), (21360692686439/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-429067777/2000000000 : ℝ)|^8379 ≤ (13038964973367/100000000000000 : ℝ)^6331
        have hw : |(-429067777/2000000000 : ℝ)|=(429067777/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2699930571/5000000000 : ℝ)|^8379 ≤ (11059912408913/25000000000000 : ℝ)^6331
        have hw : |(2699930571/5000000000 : ℝ)|=(2699930571/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1051848531/2000000000 : ℝ)|^8379 ≤ (21360692686439/50000000000000 : ℝ)^6331
        have hw : |(1051848531/2000000000 : ℝ)|=(1051848531/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1186_s4_1 (p : ℝ) (hpa : (4189/1024 : ℝ) ≤ p) (hpb : p ≤ (8379/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1336625433/2500000000 : ℝ)*x 0 + (-2216768713/10000000000 : ℝ)*x 1 + (525924287/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336625433/2500000000 : ℝ)^8379 ≤ (10915500253201/25000000000000 : ℝ)^6331 := by
    have hnat : (1336625433 : ℕ)^8379*25000000000000^6331 ≤ 10915500253201^6331*2500000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336625433 2500000000 10915500253201 25000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2216768713/10000000000 : ℝ)^8379 ≤ (6808305644019/50000000000000 : ℝ)^6331 := by
    have hnat : (2216768713 : ℕ)^8379*50000000000000^6331 ≤ 6808305644019^6331*10000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2216768713 10000000000 6808305644019 50000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (525924287/1000000000 : ℝ)^8379 ≤ (21360693842153/50000000000000 : ℝ)^6331 := by
    have hnat : (525924287 : ℕ)^8379*50000000000000^6331 ≤ 21360693842153^6331*1000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      525924287 1000000000 21360693842153 50000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8379/2048 : ℝ)) 8379 6331 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336625433/2500000000 : ℝ), (-2216768713/10000000000 : ℝ), (525924287/1000000000 : ℝ)] ![(10915500253201/25000000000000 : ℝ), (6808305644019/50000000000000 : ℝ), (21360693842153/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336625433/2500000000 : ℝ)|^8379 ≤ (10915500253201/25000000000000 : ℝ)^6331
        have hw : |(1336625433/2500000000 : ℝ)|=(1336625433/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2216768713/10000000000 : ℝ)|^8379 ≤ (6808305644019/50000000000000 : ℝ)^6331
        have hw : |(-2216768713/10000000000 : ℝ)|=(2216768713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(525924287/1000000000 : ℝ)|^8379 ≤ (21360693842153/50000000000000 : ℝ)^6331
        have hw : |(525924287/1000000000 : ℝ)|=(525924287/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1186_s4_2 (p : ℝ) (hpa : (4189/1024 : ℝ) ≤ p) (hpb : p ≤ (8379/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5346501937/10000000000 : ℝ)*x 0 + (5259242529/10000000000 : ℝ)*x 1 + (-221676889/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5346501937/10000000000 : ℝ)^8379 ≤ (5457750403561/12500000000000 : ℝ)^6331 := by
    have hnat : (5346501937 : ℕ)^8379*12500000000000^6331 ≤ 5457750403561^6331*10000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5346501937 10000000000 5457750403561 12500000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5259242529/10000000000 : ℝ)^8379 ≤ (42721384018273/100000000000000 : ℝ)^6331 := by
    have hnat : (5259242529 : ℕ)^8379*100000000000000^6331 ≤ 42721384018273^6331*10000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5259242529 10000000000 42721384018273 100000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (221676889/1000000000 : ℝ)^8379 ≤ (544664509079/4000000000000 : ℝ)^6331 := by
    have hnat : (221676889 : ℕ)^8379*4000000000000^6331 ≤ 544664509079^6331*1000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      221676889 1000000000 544664509079 4000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8379/2048 : ℝ)) 8379 6331 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5346501937/10000000000 : ℝ), (5259242529/10000000000 : ℝ), (-221676889/1000000000 : ℝ)] ![(5457750403561/12500000000000 : ℝ), (42721384018273/100000000000000 : ℝ), (544664509079/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5346501937/10000000000 : ℝ)|^8379 ≤ (5457750403561/12500000000000 : ℝ)^6331
        have hw : |(5346501937/10000000000 : ℝ)|=(5346501937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5259242529/10000000000 : ℝ)|^8379 ≤ (42721384018273/100000000000000 : ℝ)^6331
        have hw : |(5259242529/10000000000 : ℝ)|=(5259242529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-221676889/1000000000 : ℝ)|^8379 ≤ (544664509079/4000000000000 : ℝ)^6331
        have hw : |(-221676889/1000000000 : ℝ)|=(221676889/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1186_s4_3 (p : ℝ) (hpa : (4189/1024 : ℝ) ≤ p) (hpb : p ≤ (8379/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1089528451/2500000000 : ℝ)*x 0 + (4219276173/10000000000 : ℝ)*x 1 + (900289883/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1089528451/2500000000 : ℝ)^8379 ≤ (33313182626523/100000000000000 : ℝ)^6331 := by
    have hnat : (1089528451 : ℕ)^8379*100000000000000^6331 ≤ 33313182626523^6331*2500000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1089528451 2500000000 33313182626523 100000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4219276173/10000000000 : ℝ)^8379 ≤ (31915898680269/100000000000000 : ℝ)^6331 := by
    have hnat : (4219276173 : ℕ)^8379*100000000000000^6331 ≤ 31915898680269^6331*10000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4219276173 10000000000 31915898680269 100000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (900289883/2000000000 : ℝ)^8379 ≤ (34770918683873/100000000000000 : ℝ)^6331 := by
    have hnat : (900289883 : ℕ)^8379*100000000000000^6331 ≤ 34770918683873^6331*2000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      900289883 2000000000 34770918683873 100000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8379/2048 : ℝ)) 8379 6331 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1089528451/2500000000 : ℝ), (4219276173/10000000000 : ℝ), (900289883/2000000000 : ℝ)] ![(33313182626523/100000000000000 : ℝ), (31915898680269/100000000000000 : ℝ), (34770918683873/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1089528451/2500000000 : ℝ)|^8379 ≤ (33313182626523/100000000000000 : ℝ)^6331
        have hw : |(1089528451/2500000000 : ℝ)|=(1089528451/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4219276173/10000000000 : ℝ)|^8379 ≤ (31915898680269/100000000000000 : ℝ)^6331
        have hw : |(4219276173/10000000000 : ℝ)|=(4219276173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(900289883/2000000000 : ℝ)|^8379 ≤ (34770918683873/100000000000000 : ℝ)^6331
        have hw : |(900289883/2000000000 : ℝ)|=(900289883/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1186_s4_4 (p : ℝ) (hpa : (4189/1024 : ℝ) ≤ p) (hpb : p ≤ (8379/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2145345777/10000000000 : ℝ)*x 0 + (1314909433/2500000000 : ℝ)*x 1 + (5399464301/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2145345777/10000000000 : ℝ)^8379 ≤ (1303902041201/10000000000000 : ℝ)^6331 := by
    have hnat : (2145345777 : ℕ)^8379*10000000000000^6331 ≤ 1303902041201^6331*10000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2145345777 10000000000 1303902041201 10000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1314909433/2500000000 : ℝ)^8379 ≤ (10681408207539/25000000000000 : ℝ)^6331 := by
    have hnat : (1314909433 : ℕ)^8379*25000000000000^6331 ≤ 10681408207539^6331*2500000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1314909433 2500000000 10681408207539 25000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5399464301/10000000000 : ℝ)^8379 ≤ (44235346744733/100000000000000 : ℝ)^6331 := by
    have hnat : (5399464301 : ℕ)^8379*100000000000000^6331 ≤ 44235346744733^6331*10000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5399464301 10000000000 44235346744733 100000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8379/2048 : ℝ)) 8379 6331 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2145345777/10000000000 : ℝ), (1314909433/2500000000 : ℝ), (5399464301/10000000000 : ℝ)] ![(1303902041201/10000000000000 : ℝ), (10681408207539/25000000000000 : ℝ), (44235346744733/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2145345777/10000000000 : ℝ)|^8379 ≤ (1303902041201/10000000000000 : ℝ)^6331
        have hw : |(-2145345777/10000000000 : ℝ)|=(2145345777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1314909433/2500000000 : ℝ)|^8379 ≤ (10681408207539/25000000000000 : ℝ)^6331
        have hw : |(1314909433/2500000000 : ℝ)|=(1314909433/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5399464301/10000000000 : ℝ)|^8379 ≤ (44235346744733/100000000000000 : ℝ)^6331
        have hw : |(5399464301/10000000000 : ℝ)|=(5399464301/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1186_s4_5 (p : ℝ) (hpa : (4189/1024 : ℝ) ≤ p) (hpb : p ≤ (8379/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2655381681/5000000000 : ℝ)*x 0 + (-2076547023/10000000000 : ℝ)*x 1 + (5399464417/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2655381681/5000000000 : ℝ)^8379 ≤ (10819037858187/25000000000000 : ℝ)^6331 := by
    have hnat : (2655381681 : ℕ)^8379*25000000000000^6331 ≤ 10819037858187^6331*5000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2655381681 5000000000 10819037858187 25000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2076547023/10000000000 : ℝ)^8379 ≤ (3122125136573/25000000000000 : ℝ)^6331 := by
    have hnat : (2076547023 : ℕ)^8379*25000000000000^6331 ≤ 3122125136573^6331*10000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2076547023 10000000000 3122125136573 25000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5399464417/10000000000 : ℝ)^8379 ≤ (4423534800249/10000000000000 : ℝ)^6331 := by
    have hnat : (5399464417 : ℕ)^8379*10000000000000^6331 ≤ 4423534800249^6331*10000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5399464417 10000000000 4423534800249 10000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8379/2048 : ℝ)) 8379 6331 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2655381681/5000000000 : ℝ), (-2076547023/10000000000 : ℝ), (5399464417/10000000000 : ℝ)] ![(10819037858187/25000000000000 : ℝ), (3122125136573/25000000000000 : ℝ), (4423534800249/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2655381681/5000000000 : ℝ)|^8379 ≤ (10819037858187/25000000000000 : ℝ)^6331
        have hw : |(2655381681/5000000000 : ℝ)|=(2655381681/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2076547023/10000000000 : ℝ)|^8379 ≤ (3122125136573/25000000000000 : ℝ)^6331
        have hw : |(-2076547023/10000000000 : ℝ)|=(2076547023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5399464417/10000000000 : ℝ)|^8379 ≤ (4423534800249/10000000000000 : ℝ)^6331
        have hw : |(5399464417/10000000000 : ℝ)|=(5399464417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1186_s4_6 (p : ℝ) (hpa : (4189/1024 : ℝ) ≤ p) (hpb : p ≤ (8379/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5310763617/10000000000 : ℝ)*x 0 + (5399464111/10000000000 : ℝ)*x 1 + (-415309419/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5310763617/10000000000 : ℝ)^8379 ≤ (43276154182869/100000000000000 : ℝ)^6331 := by
    have hnat : (5310763617 : ℕ)^8379*100000000000000^6331 ≤ 43276154182869^6331*10000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5310763617 10000000000 43276154182869 100000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5399464111/10000000000 : ℝ)^8379 ≤ (8847068936923/20000000000000 : ℝ)^6331 := by
    have hnat : (5399464111 : ℕ)^8379*20000000000000^6331 ≤ 8847068936923^6331*10000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5399464111 10000000000 8847068936923 20000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (415309419/2000000000 : ℝ)^8379 ≤ (12488501119379/100000000000000 : ℝ)^6331 := by
    have hnat : (415309419 : ℕ)^8379*100000000000000^6331 ≤ 12488501119379^6331*2000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      415309419 2000000000 12488501119379 100000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8379/2048 : ℝ)) 8379 6331 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5310763617/10000000000 : ℝ), (5399464111/10000000000 : ℝ), (-415309419/2000000000 : ℝ)] ![(43276154182869/100000000000000 : ℝ), (8847068936923/20000000000000 : ℝ), (12488501119379/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5310763617/10000000000 : ℝ)|^8379 ≤ (43276154182869/100000000000000 : ℝ)^6331
        have hw : |(5310763617/10000000000 : ℝ)|=(5310763617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5399464111/10000000000 : ℝ)|^8379 ≤ (8847068936923/20000000000000 : ℝ)^6331
        have hw : |(5399464111/10000000000 : ℝ)|=(5399464111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-415309419/2000000000 : ℝ)|^8379 ≤ (12488501119379/100000000000000 : ℝ)^6331
        have hw : |(-415309419/2000000000 : ℝ)|=(415309419/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1186_s4_7 (p : ℝ) (hpa : (4189/1024 : ℝ) ≤ p) (hpb : p ≤ (8379/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (136191481/312500000 : ℝ)*x 0 + (4500656063/10000000000 : ℝ)*x 1 + (844014507/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (136191481/312500000 : ℝ)^8379 ≤ (33313320091857/100000000000000 : ℝ)^6331 := by
    have hnat : (136191481 : ℕ)^8379*100000000000000^6331 ≤ 33313320091857^6331*312500000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      136191481 312500000 33313320091857 100000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4500656063/10000000000 : ℝ)^8379 ≤ (34762808378473/100000000000000 : ℝ)^6331 := by
    have hnat : (4500656063 : ℕ)^8379*100000000000000^6331 ≤ 34762808378473^6331*10000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4500656063 10000000000 34762808378473 100000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (844014507/2000000000 : ℝ)^8379 ≤ (1276954860619/4000000000000 : ℝ)^6331 := by
    have hnat : (844014507 : ℕ)^8379*4000000000000^6331 ≤ 1276954860619^6331*2000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      844014507 2000000000 1276954860619 4000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8379/2048 : ℝ)) 8379 6331 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(136191481/312500000 : ℝ), (4500656063/10000000000 : ℝ), (844014507/2000000000 : ℝ)] ![(33313320091857/100000000000000 : ℝ), (34762808378473/100000000000000 : ℝ), (1276954860619/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(136191481/312500000 : ℝ)|^8379 ≤ (33313320091857/100000000000000 : ℝ)^6331
        have hw : |(136191481/312500000 : ℝ)|=(136191481/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4500656063/10000000000 : ℝ)|^8379 ≤ (34762808378473/100000000000000 : ℝ)^6331
        have hw : |(4500656063/10000000000 : ℝ)|=(4500656063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(844014507/2000000000 : ℝ)|^8379 ≤ (1276954860619/4000000000000 : ℝ)^6331
        have hw : |(844014507/2000000000 : ℝ)|=(844014507/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1186_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4189/1024 : ℝ) ≤ p) (hpb : p ≤ (8379/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150332923/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3689/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5381/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (1407/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7117/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3689/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5381/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3689/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5381/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3689/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5381/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3689/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5381/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3689/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5381/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3689/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5381/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5381/50000 : ℝ) ^ (4189/1024 : ℝ) ≤ (10955902771832741/100000000000000000000 : ℝ) := by
    have hpowers : (5381/50000 : ℝ)^4189 ≤ (10955902771832741/100000000000000000000 : ℝ)^1024 := by
      have hnat : (5381 : ℕ)^4189*100000000000000000000^1024 ≤ 10955902771832741^1024*50000^4189 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5381 50000 10955902771832741 100000000000000000000 4189 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5381/50000 : ℝ)) (X := (10955902771832741/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4189 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3689/25000 : ℝ) ^ (4189/1024 : ℝ) ≤ (39847406385319239/100000000000000000000 : ℝ) := by
    have hpowers : (3689/25000 : ℝ)^4189 ≤ (39847406385319239/100000000000000000000 : ℝ)^1024 := by
      have hnat : (3689 : ℕ)^4189*100000000000000000000^1024 ≤ 39847406385319239^1024*25000^4189 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3689 25000 39847406385319239 100000000000000000000 4189 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3689/25000 : ℝ)) (X := (39847406385319239/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4189 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010955902771832741/50000000000000000000 : ℝ) ≤ (10000535589204641/10000000000000000 : ℝ) ^ (4189/1024 : ℝ) := by
    have hpowers : (50010955902771832741/50000000000000000000 : ℝ)^1024 ≤ (10000535589204641/10000000000000000 : ℝ)^4189 := by
      have hnat : (50010955902771832741 : ℕ)^1024*10000000000000000^4189 ≤ 10000535589204641^4189*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010955902771832741 50000000000000000000 10000535589204641 10000000000000000 1024 4189 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000535589204641/10000000000000000 : ℝ)) (X := (50010955902771832741/50000000000000000000 : ℝ)) (by norm_num) 4189 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (5002540165457857599/5000000000000000000 : ℝ) ≤ (5000620823672131/5000000000000000 : ℝ) ^ (4189/1024 : ℝ) := by
    have hpowers : (5002540165457857599/5000000000000000000 : ℝ)^1024 ≤ (5000620823672131/5000000000000000 : ℝ)^4189 := by
      have hnat : (5002540165457857599 : ℕ)^1024*5000000000000000^4189 ≤ 5000620823672131^4189*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5002540165457857599 5000000000000000000 5000620823672131 5000000000000000 1024 4189 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000620823672131/5000000000000000 : ℝ)) (X := (5002540165457857599/5000000000000000000 : ℝ)) (by norm_num) 4189 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50039847406385319239/50000000000000000000 : ℝ) ≤ (10001947705483883/10000000000000000 : ℝ) ^ (4189/1024 : ℝ) := by
    have hpowers : (50039847406385319239/50000000000000000000 : ℝ)^1024 ≤ (10001947705483883/10000000000000000 : ℝ)^4189 := by
      have hnat : (50039847406385319239 : ℕ)^1024*10000000000000000^4189 ≤ 10001947705483883^4189*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50039847406385319239 50000000000000000000 10001947705483883 10000000000000000 1024 4189 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001947705483883/10000000000000000 : ℝ)) (X := (50039847406385319239/50000000000000000000 : ℝ)) (by norm_num) 4189 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10955902771832741/100000000000000000000 : ℝ) ≤ ((31941553558308907/31952000000000000 : ℝ)+2*(706058139621/399400000000000 : ℝ)*(5381/50000 : ℝ))^(4189/1024 : ℝ) := by
    rw [show (31941553558308907/31952000000000000 : ℝ)+2*(706058139621/399400000000000 : ℝ)*(5381/50000 : ℝ)=(10000535589204641/10000000000000000 : ℝ) by norm_num, show 1+2*(10955902771832741/100000000000000000000 : ℝ)=(50010955902771832741/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(39847406385319239/100000000000000000000 : ℝ)+(10955902771832741/100000000000000000000 : ℝ) ≤ ((31941553558308907/31952000000000000 : ℝ)+(706058139621/399400000000000 : ℝ)*((3689/25000 : ℝ)+(5381/50000 : ℝ)))^(4189/1024 : ℝ) := by
    rw [show (31941553558308907/31952000000000000 : ℝ)+(706058139621/399400000000000 : ℝ)*((3689/25000 : ℝ)+(5381/50000 : ℝ))=(5000620823672131/5000000000000000 : ℝ) by norm_num, show 1+(39847406385319239/100000000000000000000 : ℝ)+(10955902771832741/100000000000000000000 : ℝ)=(5002540165457857599/5000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(39847406385319239/100000000000000000000 : ℝ) ≤ ((31941553558308907/31952000000000000 : ℝ)+2*(706058139621/399400000000000 : ℝ)*(3689/25000 : ℝ))^(4189/1024 : ℝ) := by
    rw [show (31941553558308907/31952000000000000 : ℝ)+2*(706058139621/399400000000000 : ℝ)*(3689/25000 : ℝ)=(10001947705483883/10000000000000000 : ℝ) by norm_num, show 1+2*(39847406385319239/100000000000000000000 : ℝ)=(50039847406385319239/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (31941553558308907/31952000000000000 : ℝ)*(X 1 0+X 2 0)+(706058139621/399400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4189/1024 : ℝ)) (lo := (5381/50000 : ℝ)) (hi := (3689/25000 : ℝ)) (c := (31941553558308907/31952000000000000 : ℝ)) (alpha := (706058139621/399400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (31941553558308907/31952000000000000 : ℝ)*(X 0 1+X 2 1)+(706058139621/399400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4189/1024 : ℝ)) (lo := (5381/50000 : ℝ)) (hi := (3689/25000 : ℝ)) (c := (31941553558308907/31952000000000000 : ℝ)) (alpha := (706058139621/399400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (31941553558308907/31952000000000000 : ℝ)*(X 0 2+X 1 2)+(706058139621/399400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4189/1024 : ℝ)) (lo := (5381/50000 : ℝ)) (hi := (3689/25000 : ℝ)) (c := (31941553558308907/31952000000000000 : ℝ)) (alpha := (706058139621/399400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-429067777/2000000000 : ℝ)*X 0 0+(2699930571/5000000000 : ℝ)*X 0 1+(1051848531/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1186_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1336625433/2500000000 : ℝ)*X 1 0+(-2216768713/10000000000 : ℝ)*X 1 1+(525924287/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1186_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5346501937/10000000000 : ℝ)*X 2 0+(5259242529/10000000000 : ℝ)*X 2 1+(-221676889/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1186_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1089528451/2500000000 : ℝ)*X 0 0+(4219276173/10000000000 : ℝ)*X 0 1+(900289883/2000000000 : ℝ)*X 0 2+(1089528451/2500000000 : ℝ)*X 1 0+(4219276173/10000000000 : ℝ)*X 1 1+(900289883/2000000000 : ℝ)*X 1 2+(1089528451/2500000000 : ℝ)*X 2 0+(4219276173/10000000000 : ℝ)*X 2 1+(900289883/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1186_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2145345777/10000000000 : ℝ)*X 0 0+(1314909433/2500000000 : ℝ)*X 0 1+(5399464301/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1186_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2655381681/5000000000 : ℝ)*X 1 0+(-2076547023/10000000000 : ℝ)*X 1 1+(5399464417/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1186_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5310763617/10000000000 : ℝ)*X 2 0+(5399464111/10000000000 : ℝ)*X 2 1+(-415309419/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1186_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((136191481/312500000 : ℝ)*X 0 0+(4500656063/10000000000 : ℝ)*X 0 1+(844014507/2000000000 : ℝ)*X 0 2+(136191481/312500000 : ℝ)*X 1 0+(4500656063/10000000000 : ℝ)*X 1 1+(844014507/2000000000 : ℝ)*X 1 2+(136191481/312500000 : ℝ)*X 2 0+(4500656063/10000000000 : ℝ)*X 2 1+(844014507/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1186_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3350127664608785956581399/319520000000000000000000000000 : ℝ) := by norm_num
    linear_combination (10736753/781250000000 : ℝ)*(base19) + (1629104997/100000000000000 : ℝ)*(base23) + (9034473/3125000000000 : ℝ)*(upper3) + (9556953/100000000000000 : ℝ)*(upper4) + (33289607/50000000000000 : ℝ)*(upper5) + (1065548326703747/20000000000000 : ℝ)*(major0) + (1065548326703747/20000000000000 : ℝ)*(major1) + (1065548326703747/20000000000000 : ℝ)*(major2) + (1777871046978169/25000000000000 : ℝ)*(sp0) + (1777879890979579/25000000000000 : ℝ)*(sp1) + (3555759654558851/50000000000000 : ℝ)*(sp2) + (3543939282899833/100000000000000 : ℝ)*(sp3) + (36750310023/100000000000000 : ℝ)*(sp4) + (5674104763/25000000000000 : ℝ)*(sp7) + (1771980989659443/50000000000000 : ℝ)*(f.failure) + (7111520938222699/100000000000000 : ℝ)*(f.sum) + (16384802547797/3994000000000000000000000000 : ℝ)*base65 + (5696671119449969/639040000000000000000000000000 : ℝ)*base67 + (1904701695134769/639040000000000000000000000000 : ℝ)*base69 + (4753911246056369/639040000000000000000000000000 : ℝ)*base71 + (25126845416349/3994000000000000000000000000 : ℝ)*base73 + (7157595658543089/639040000000000000000000000000 : ℝ)*base75 + (2003824677219889/639040000000000000000000000000 : ℝ)*base77 + (5099216947798769/639040000000000000000000000000 : ℝ)*base79 + (17470947882297/3994000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (90741889/5000000000000000000000 : ℝ)*base89 + (90741889/5000000000000000000000 : ℝ)*base91 + (90741889/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (20463668582053810467471/9985000000000000000000000000 : ℝ) := by norm_num
    linear_combination (132743221/20000000000000 : ℝ)*(base19) + (257352879/20000000000000 : ℝ)*(base23) + (9785801/6250000000000 : ℝ)*(upper2) + (16301423/100000000000000 : ℝ)*(upper3) + (234248937/100000000000000 : ℝ)*(upper5) + (2678930602727651/50000000000000 : ℝ)*(major0) + (2678930602727651/50000000000000 : ℝ)*(major1) + (2678930602727651/50000000000000 : ℝ)*(major2) + (1658106191/6250000000000 : ℝ)*(sp1) + (4855138599/20000000000000 : ℝ)*(sp2) + (7151725116615459/100000000000000 : ℝ)*(sp4) + (3575848961600149/50000000000000 : ℝ)*(sp5) + (715169955415807/10000000000000 : ℝ)*(sp6) + (1781998612990217/50000000000000 : ℝ)*(sp7) + (1781998612990217/50000000000000 : ℝ)*(f.failure) + (7151725116615459/100000000000000 : ℝ)*(f.sum) + (17601986866273/4992500000000000000000000000 : ℝ)*base65 + (16519129678101137/1597600000000000000000000000000 : ℝ)*base67 + (10200473138653263/1597600000000000000000000000000 : ℝ)*base70 + (23554760911699537/1597600000000000000000000000000 : ℝ)*base71 + (21848616113671/9985000000000000000000000000 : ℝ)*base73 + (7825317747068463/1597600000000000000000000000000 : ℝ)*base76 + (32726384989228337/1597600000000000000000000000000 : ℝ)*base77 + (34199096514370063/1597600000000000000000000000000 : ℝ)*base80 + (14618233680121/9985000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (7985709/5000000000000000000000 : ℝ)*base90 + (7985709/5000000000000000000000 : ℝ)*base92 + (7985709/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1186_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4189/1024 : ℝ) ≤ p) (hpb : p ≤ (8379/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150332923/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3689/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5381/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1407/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7117/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1186_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1186_s5_0 (p : ℝ) (hpa : (4189/1024 : ℝ) ≤ p) (hpb : p ≤ (8379/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2145888693/10000000000 : ℝ)*x 0 + (337111439/625000000 : ℝ)*x 1 + (1316239841/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2145888693/10000000000 : ℝ)^8379 ≤ (3260846940403/25000000000000 : ℝ)^6331 := by
    have hnat : (2145888693 : ℕ)^8379*25000000000000^6331 ≤ 3260846940403^6331*10000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2145888693 10000000000 3260846940403 25000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (337111439/625000000 : ℝ)^8379 ≤ (883475133577/2000000000000 : ℝ)^6331 := by
    have hnat : (337111439 : ℕ)^8379*2000000000000^6331 ≤ 883475133577^6331*625000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337111439 625000000 883475133577 2000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316239841/2500000000 : ℝ)^8379 ≤ (10695713885579/25000000000000 : ℝ)^6331 := by
    have hnat : (1316239841 : ℕ)^8379*25000000000000^6331 ≤ 10695713885579^6331*2500000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316239841 2500000000 10695713885579 25000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8379/2048 : ℝ)) 8379 6331 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2145888693/10000000000 : ℝ), (337111439/625000000 : ℝ), (1316239841/2500000000 : ℝ)] ![(3260846940403/25000000000000 : ℝ), (883475133577/2000000000000 : ℝ), (10695713885579/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2145888693/10000000000 : ℝ)|^8379 ≤ (3260846940403/25000000000000 : ℝ)^6331
        have hw : |(-2145888693/10000000000 : ℝ)|=(2145888693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(337111439/625000000 : ℝ)|^8379 ≤ (883475133577/2000000000000 : ℝ)^6331
        have hw : |(337111439/625000000 : ℝ)|=(337111439/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316239841/2500000000 : ℝ)|^8379 ≤ (10695713885579/25000000000000 : ℝ)^6331
        have hw : |(1316239841/2500000000 : ℝ)|=(1316239841/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1186_s5_1 (p : ℝ) (hpa : (4189/1024 : ℝ) ≤ p) (hpb : p ≤ (8379/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344970481/10000000000 : ℝ)*x 0 + (-552810291/2500000000 : ℝ)*x 1 + (2632479683/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344970481/10000000000 : ℝ)^8379 ≤ (872909033923/2000000000000 : ℝ)^6331 := by
    have hnat : (5344970481 : ℕ)^8379*2000000000000^6331 ≤ 872909033923^6331*10000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344970481 10000000000 872909033923 2000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (552810291/2500000000 : ℝ)^8379 ≤ (6785846362993/50000000000000 : ℝ)^6331 := by
    have hnat : (552810291 : ℕ)^8379*50000000000000^6331 ≤ 6785846362993^6331*2500000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      552810291 2500000000 6785846362993 50000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632479683/5000000000 : ℝ)^8379 ≤ (1711314222553/4000000000000 : ℝ)^6331 := by
    have hnat : (2632479683 : ℕ)^8379*4000000000000^6331 ≤ 1711314222553^6331*5000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632479683 5000000000 1711314222553 4000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8379/2048 : ℝ)) 8379 6331 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344970481/10000000000 : ℝ), (-552810291/2500000000 : ℝ), (2632479683/5000000000 : ℝ)] ![(872909033923/2000000000000 : ℝ), (6785846362993/50000000000000 : ℝ), (1711314222553/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344970481/10000000000 : ℝ)|^8379 ≤ (872909033923/2000000000000 : ℝ)^6331
        have hw : |(5344970481/10000000000 : ℝ)|=(5344970481/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-552810291/2500000000 : ℝ)|^8379 ≤ (6785846362993/50000000000000 : ℝ)^6331
        have hw : |(-552810291/2500000000 : ℝ)|=(552810291/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632479683/5000000000 : ℝ)|^8379 ≤ (1711314222553/4000000000000 : ℝ)^6331
        have hw : |(2632479683/5000000000 : ℝ)|=(2632479683/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1186_s5_2 (p : ℝ) (hpa : (4189/1024 : ℝ) ≤ p) (hpb : p ≤ (8379/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1336242619/2500000000 : ℝ)*x 0 + (1316239843/2500000000 : ℝ)*x 1 + (-2211241163/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336242619/2500000000 : ℝ)^8379 ≤ (21822725821057/50000000000000 : ℝ)^6331 := by
    have hnat : (1336242619 : ℕ)^8379*50000000000000^6331 ≤ 21822725821057^6331*2500000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336242619 2500000000 21822725821057 50000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316239843/2500000000 : ℝ)^8379 ≤ (668482119193/1562500000000 : ℝ)^6331 := by
    have hnat : (1316239843 : ℕ)^8379*1562500000000^6331 ≤ 668482119193^6331*2500000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316239843 2500000000 668482119193 1562500000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2211241163/10000000000 : ℝ)^8379 ≤ (13571692717863/100000000000000 : ℝ)^6331 := by
    have hnat : (2211241163 : ℕ)^8379*100000000000000^6331 ≤ 13571692717863^6331*10000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2211241163 10000000000 13571692717863 100000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8379/2048 : ℝ)) 8379 6331 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336242619/2500000000 : ℝ), (1316239843/2500000000 : ℝ), (-2211241163/10000000000 : ℝ)] ![(21822725821057/50000000000000 : ℝ), (668482119193/1562500000000 : ℝ), (13571692717863/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336242619/2500000000 : ℝ)|^8379 ≤ (21822725821057/50000000000000 : ℝ)^6331
        have hw : |(1336242619/2500000000 : ℝ)|=(1336242619/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316239843/2500000000 : ℝ)|^8379 ≤ (668482119193/1562500000000 : ℝ)^6331
        have hw : |(1316239843/2500000000 : ℝ)|=(1316239843/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2211241163/10000000000 : ℝ)|^8379 ≤ (13571692717863/100000000000000 : ℝ)^6331
        have hw : |(-2211241163/10000000000 : ℝ)|=(2211241163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1186_s5_3 (p : ℝ) (hpa : (4189/1024 : ℝ) ≤ p) (hpb : p ≤ (8379/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1089608477/2500000000 : ℝ)*x 0 + (169242757/400000000 : ℝ)*x 1 + (1122393497/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1089608477/2500000000 : ℝ)^8379 ≤ (4164552631303/12500000000000 : ℝ)^6331 := by
    have hnat : (1089608477 : ℕ)^8379*12500000000000^6331 ≤ 4164552631303^6331*2500000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1089608477 2500000000 4164552631303 12500000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (169242757/400000000 : ℝ)^8379 ≤ (3203401239547/10000000000000 : ℝ)^6331 := by
    have hnat : (169242757 : ℕ)^8379*10000000000000^6331 ≤ 3203401239547^6331*400000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169242757 400000000 3203401239547 10000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1122393497/2500000000 : ℝ)^8379 ≤ (6929913308837/20000000000000 : ℝ)^6331 := by
    have hnat : (1122393497 : ℕ)^8379*20000000000000^6331 ≤ 6929913308837^6331*2500000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1122393497 2500000000 6929913308837 20000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8379/2048 : ℝ)) 8379 6331 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1089608477/2500000000 : ℝ), (169242757/400000000 : ℝ), (1122393497/2500000000 : ℝ)] ![(4164552631303/12500000000000 : ℝ), (3203401239547/10000000000000 : ℝ), (6929913308837/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1089608477/2500000000 : ℝ)|^8379 ≤ (4164552631303/12500000000000 : ℝ)^6331
        have hw : |(1089608477/2500000000 : ℝ)|=(1089608477/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(169242757/400000000 : ℝ)|^8379 ≤ (3203401239547/10000000000000 : ℝ)^6331
        have hw : |(169242757/400000000 : ℝ)|=(169242757/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1122393497/2500000000 : ℝ)|^8379 ≤ (6929913308837/20000000000000 : ℝ)^6331
        have hw : |(1122393497/2500000000 : ℝ)|=(1122393497/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1186_s5_4 (p : ℝ) (hpa : (4189/1024 : ℝ) ≤ p) (hpb : p ≤ (8379/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2145893823/10000000000 : ℝ)*x 0 + (5265291289/10000000000 : ℝ)*x 1 + (5393449871/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2145893823/10000000000 : ℝ)^8379 ≤ (13043429030297/100000000000000 : ℝ)^6331 := by
    have hnat : (2145893823 : ℕ)^8379*100000000000000^6331 ≤ 13043429030297^6331*10000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2145893823 10000000000 13043429030297 100000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265291289/10000000000 : ℝ)^8379 ≤ (1711457012091/4000000000000 : ℝ)^6331 := by
    have hnat : (5265291289 : ℕ)^8379*4000000000000^6331 ≤ 1711457012091^6331*10000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265291289 10000000000 1711457012091 4000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5393449871/10000000000 : ℝ)^8379 ≤ (22085072828447/50000000000000 : ℝ)^6331 := by
    have hnat : (5393449871 : ℕ)^8379*50000000000000^6331 ≤ 22085072828447^6331*10000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393449871 10000000000 22085072828447 50000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8379/2048 : ℝ)) 8379 6331 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2145893823/10000000000 : ℝ), (5265291289/10000000000 : ℝ), (5393449871/10000000000 : ℝ)] ![(13043429030297/100000000000000 : ℝ), (1711457012091/4000000000000 : ℝ), (22085072828447/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2145893823/10000000000 : ℝ)|^8379 ≤ (13043429030297/100000000000000 : ℝ)^6331
        have hw : |(-2145893823/10000000000 : ℝ)|=(2145893823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265291289/10000000000 : ℝ)|^8379 ≤ (1711457012091/4000000000000 : ℝ)^6331
        have hw : |(5265291289/10000000000 : ℝ)|=(5265291289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5393449871/10000000000 : ℝ)|^8379 ≤ (22085072828447/50000000000000 : ℝ)^6331
        have hw : |(5393449871/10000000000 : ℝ)|=(5393449871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1186_s5_5 (p : ℝ) (hpa : (4189/1024 : ℝ) ≤ p) (hpb : p ≤ (8379/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312228423/10000000000 : ℝ)*x 0 + (-416550121/2000000000 : ℝ)*x 1 + (2696724923/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312228423/10000000000 : ℝ)^8379 ≤ (43291952508031/100000000000000 : ℝ)^6331 := by
    have hnat : (5312228423 : ℕ)^8379*100000000000000^6331 ≤ 43291952508031^6331*10000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312228423 10000000000 43291952508031 100000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (416550121/2000000000 : ℝ)^8379 ≤ (12537902098091/100000000000000 : ℝ)^6331 := by
    have hnat : (416550121 : ℕ)^8379*100000000000000^6331 ≤ 12537902098091^6331*2000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      416550121 2000000000 12537902098091 100000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2696724923/5000000000 : ℝ)^8379 ≤ (11042536346481/25000000000000 : ℝ)^6331 := by
    have hnat : (2696724923 : ℕ)^8379*25000000000000^6331 ≤ 11042536346481^6331*5000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696724923 5000000000 11042536346481 25000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8379/2048 : ℝ)) 8379 6331 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312228423/10000000000 : ℝ), (-416550121/2000000000 : ℝ), (2696724923/5000000000 : ℝ)] ![(43291952508031/100000000000000 : ℝ), (12537902098091/100000000000000 : ℝ), (11042536346481/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312228423/10000000000 : ℝ)|^8379 ≤ (43291952508031/100000000000000 : ℝ)^6331
        have hw : |(5312228423/10000000000 : ℝ)|=(5312228423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-416550121/2000000000 : ℝ)|^8379 ≤ (12537902098091/100000000000000 : ℝ)^6331
        have hw : |(-416550121/2000000000 : ℝ)|=(416550121/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2696724923/5000000000 : ℝ)|^8379 ≤ (11042536346481/25000000000000 : ℝ)^6331
        have hw : |(2696724923/5000000000 : ℝ)|=(2696724923/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1186_s5_6 (p : ℝ) (hpa : (4189/1024 : ℝ) ≤ p) (hpb : p ≤ (8379/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2656114141/5000000000 : ℝ)*x 0 + (2696724999/5000000000 : ℝ)*x 1 + (-2082750589/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656114141/5000000000 : ℝ)^8379 ≤ (43291950987241/100000000000000 : ℝ)^6331 := by
    have hnat : (2656114141 : ℕ)^8379*100000000000000^6331 ≤ 43291950987241^6331*5000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656114141 5000000000 43291950987241 100000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2696724999/5000000000 : ℝ)^8379 ≤ (2760634189589/6250000000000 : ℝ)^6331 := by
    have hnat : (2696724999 : ℕ)^8379*6250000000000^6331 ≤ 2760634189589^6331*5000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696724999 5000000000 2760634189589 6250000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2082750589/10000000000 : ℝ)^8379 ≤ (2507580394123/20000000000000 : ℝ)^6331 := by
    have hnat : (2082750589 : ℕ)^8379*20000000000000^6331 ≤ 2507580394123^6331*10000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2082750589 10000000000 2507580394123 20000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8379/2048 : ℝ)) 8379 6331 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656114141/5000000000 : ℝ), (2696724999/5000000000 : ℝ), (-2082750589/10000000000 : ℝ)] ![(43291950987241/100000000000000 : ℝ), (2760634189589/6250000000000 : ℝ), (2507580394123/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656114141/5000000000 : ℝ)|^8379 ≤ (43291950987241/100000000000000 : ℝ)^6331
        have hw : |(2656114141/5000000000 : ℝ)|=(2656114141/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2696724999/5000000000 : ℝ)|^8379 ≤ (2760634189589/6250000000000 : ℝ)^6331
        have hw : |(2696724999/5000000000 : ℝ)|=(2696724999/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2082750589/10000000000 : ℝ)|^8379 ≤ (2507580394123/20000000000000 : ℝ)^6331
        have hw : |(-2082750589/10000000000 : ℝ)|=(2082750589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1186_s5_7 (p : ℝ) (hpa : (4189/1024 : ℝ) ≤ p) (hpb : p ≤ (8379/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2179222081/5000000000 : ℝ)*x 0 + (4488907921/10000000000 : ℝ)*x 1 + (2115868753/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2179222081/5000000000 : ℝ)^8379 ≤ (33316524789227/100000000000000 : ℝ)^6331 := by
    have hnat : (2179222081 : ℕ)^8379*100000000000000^6331 ≤ 33316524789227^6331*5000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2179222081 5000000000 33316524789227 100000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4488907921/10000000000 : ℝ)^8379 ≤ (34642763237557/100000000000000 : ℝ)^6331 := by
    have hnat : (4488907921 : ℕ)^8379*100000000000000^6331 ≤ 34642763237557^6331*10000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4488907921 10000000000 34642763237557 100000000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2115868753/5000000000 : ℝ)^8379 ≤ (2002544497183/6250000000000 : ℝ)^6331 := by
    have hnat : (2115868753 : ℕ)^8379*6250000000000^6331 ≤ 2002544497183^6331*5000000000^8379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2115868753 5000000000 2002544497183 6250000000000 8379 6331 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8379/2048 : ℝ)) 8379 6331 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2179222081/5000000000 : ℝ), (4488907921/10000000000 : ℝ), (2115868753/5000000000 : ℝ)] ![(33316524789227/100000000000000 : ℝ), (34642763237557/100000000000000 : ℝ), (2002544497183/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2179222081/5000000000 : ℝ)|^8379 ≤ (33316524789227/100000000000000 : ℝ)^6331
        have hw : |(2179222081/5000000000 : ℝ)|=(2179222081/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4488907921/10000000000 : ℝ)|^8379 ≤ (34642763237557/100000000000000 : ℝ)^6331
        have hw : |(4488907921/10000000000 : ℝ)|=(4488907921/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2115868753/5000000000 : ℝ)|^8379 ≤ (2002544497183/6250000000000 : ℝ)^6331
        have hw : |(2115868753/5000000000 : ℝ)|=(2115868753/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1186_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4189/1024 : ℝ) ≤ p) (hpb : p ≤ (8379/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150332923/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7117/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1407/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (5689/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14107/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7117/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1407/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7117/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1407/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7117/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1407/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7117/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1407/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7117/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1407/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7117/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1407/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1407/12500 : ℝ) ^ (4189/1024 : ℝ) ≤ (6581922255026979/50000000000000000000 : ℝ) := by
    have hpowers : (1407/12500 : ℝ)^4189 ≤ (6581922255026979/50000000000000000000 : ℝ)^1024 := by
      have hnat : (1407 : ℕ)^4189*50000000000000000000^1024 ≤ 6581922255026979^1024*12500^4189 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1407 12500 6581922255026979 50000000000000000000 4189 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1407/12500 : ℝ)) (X := (6581922255026979/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4189 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7117/50000 : ℝ) ^ (4189/1024 : ℝ) ≤ (34388460676278989/100000000000000000000 : ℝ) := by
    have hpowers : (7117/50000 : ℝ)^4189 ≤ (34388460676278989/100000000000000000000 : ℝ)^1024 := by
      have hnat : (7117 : ℕ)^4189*100000000000000000000^1024 ≤ 34388460676278989^1024*50000^4189 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7117 50000 34388460676278989 100000000000000000000 4189 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7117/50000 : ℝ)) (X := (34388460676278989/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4189 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25006581922255026979/25000000000000000000 : ℝ) ≤ (10000643515697947/10000000000000000 : ℝ) ^ (4189/1024 : ℝ) := by
    have hpowers : (25006581922255026979/25000000000000000000 : ℝ)^1024 ≤ (10000643515697947/10000000000000000 : ℝ)^4189 := by
      have hnat : (25006581922255026979 : ℕ)^1024*10000000000000000^4189 ≤ 10000643515697947^4189*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25006581922255026979 25000000000000000000 10000643515697947 10000000000000000 1024 4189 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000643515697947/10000000000000000 : ℝ)) (X := (25006581922255026979/25000000000000000000 : ℝ)) (by norm_num) 4189 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100047552305186332947/100000000000000000000 : ℝ) ≤ (5000581103074659/5000000000000000 : ℝ) ^ (4189/1024 : ℝ) := by
    have hpowers : (100047552305186332947/100000000000000000000 : ℝ)^1024 ≤ (5000581103074659/5000000000000000 : ℝ)^4189 := by
      have hnat : (100047552305186332947 : ℕ)^1024*5000000000000000^4189 ≤ 5000581103074659^4189*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100047552305186332947 100000000000000000000 5000581103074659 5000000000000000 1024 4189 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000581103074659/5000000000000000 : ℝ)) (X := (100047552305186332947/100000000000000000000 : ℝ)) (by norm_num) 4189 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50034388460676278989/50000000000000000000 : ℝ) ≤ (10001680896600689/10000000000000000 : ℝ) ^ (4189/1024 : ℝ) := by
    have hpowers : (50034388460676278989/50000000000000000000 : ℝ)^1024 ≤ (10001680896600689/10000000000000000 : ℝ)^4189 := by
      have hnat : (50034388460676278989 : ℕ)^1024*10000000000000000^4189 ≤ 10001680896600689^4189*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50034388460676278989 50000000000000000000 10001680896600689 10000000000000000 1024 4189 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001680896600689/10000000000000000 : ℝ)) (X := (50034388460676278989/50000000000000000000 : ℝ)) (by norm_num) 4189 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6581922255026979/50000000000000000000 : ℝ) ≤ ((14885119815153611107/14890000000000000000 : ℝ)+2*(518690451371/297800000000000 : ℝ)*(1407/12500 : ℝ))^(4189/1024 : ℝ) := by
    rw [show (14885119815153611107/14890000000000000000 : ℝ)+2*(518690451371/297800000000000 : ℝ)*(1407/12500 : ℝ)=(10000643515697947/10000000000000000 : ℝ) by norm_num, show 1+2*(6581922255026979/50000000000000000000 : ℝ)=(25006581922255026979/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(34388460676278989/100000000000000000000 : ℝ)+(6581922255026979/50000000000000000000 : ℝ) ≤ ((14885119815153611107/14890000000000000000 : ℝ)+(518690451371/297800000000000 : ℝ)*((7117/50000 : ℝ)+(1407/12500 : ℝ)))^(4189/1024 : ℝ) := by
    rw [show (14885119815153611107/14890000000000000000 : ℝ)+(518690451371/297800000000000 : ℝ)*((7117/50000 : ℝ)+(1407/12500 : ℝ))=(5000581103074659/5000000000000000 : ℝ) by norm_num, show 1+(34388460676278989/100000000000000000000 : ℝ)+(6581922255026979/50000000000000000000 : ℝ)=(100047552305186332947/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(34388460676278989/100000000000000000000 : ℝ) ≤ ((14885119815153611107/14890000000000000000 : ℝ)+2*(518690451371/297800000000000 : ℝ)*(7117/50000 : ℝ))^(4189/1024 : ℝ) := by
    rw [show (14885119815153611107/14890000000000000000 : ℝ)+2*(518690451371/297800000000000 : ℝ)*(7117/50000 : ℝ)=(10001680896600689/10000000000000000 : ℝ) by norm_num, show 1+2*(34388460676278989/100000000000000000000 : ℝ)=(50034388460676278989/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (14885119815153611107/14890000000000000000 : ℝ)*(X 1 0+X 2 0)+(518690451371/297800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4189/1024 : ℝ)) (lo := (1407/12500 : ℝ)) (hi := (7117/50000 : ℝ)) (c := (14885119815153611107/14890000000000000000 : ℝ)) (alpha := (518690451371/297800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (14885119815153611107/14890000000000000000 : ℝ)*(X 0 1+X 2 1)+(518690451371/297800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4189/1024 : ℝ)) (lo := (1407/12500 : ℝ)) (hi := (7117/50000 : ℝ)) (c := (14885119815153611107/14890000000000000000 : ℝ)) (alpha := (518690451371/297800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (14885119815153611107/14890000000000000000 : ℝ)*(X 0 2+X 1 2)+(518690451371/297800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4189/1024 : ℝ)) (lo := (1407/12500 : ℝ)) (hi := (7117/50000 : ℝ)) (c := (14885119815153611107/14890000000000000000 : ℝ)) (alpha := (518690451371/297800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2145888693/10000000000 : ℝ)*X 0 0+(337111439/625000000 : ℝ)*X 0 1+(1316239841/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1186_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344970481/10000000000 : ℝ)*X 1 0+(-552810291/2500000000 : ℝ)*X 1 1+(2632479683/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1186_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1336242619/2500000000 : ℝ)*X 2 0+(1316239843/2500000000 : ℝ)*X 2 1+(-2211241163/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1186_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1089608477/2500000000 : ℝ)*X 0 0+(169242757/400000000 : ℝ)*X 0 1+(1122393497/2500000000 : ℝ)*X 0 2+(1089608477/2500000000 : ℝ)*X 1 0+(169242757/400000000 : ℝ)*X 1 1+(1122393497/2500000000 : ℝ)*X 1 2+(1089608477/2500000000 : ℝ)*X 2 0+(169242757/400000000 : ℝ)*X 2 1+(1122393497/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1186_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2145893823/10000000000 : ℝ)*X 0 0+(5265291289/10000000000 : ℝ)*X 0 1+(5393449871/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1186_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312228423/10000000000 : ℝ)*X 1 0+(-416550121/2000000000 : ℝ)*X 1 1+(2696724923/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1186_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2656114141/5000000000 : ℝ)*X 2 0+(2696724999/5000000000 : ℝ)*X 2 1+(-2082750589/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1186_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2179222081/5000000000 : ℝ)*X 0 0+(4488907921/10000000000 : ℝ)*X 0 1+(2115868753/5000000000 : ℝ)*X 0 2+(2179222081/5000000000 : ℝ)*X 1 0+(4488907921/10000000000 : ℝ)*X 1 1+(2115868753/5000000000 : ℝ)*X 1 2+(2179222081/5000000000 : ℝ)*X 2 0+(4488907921/10000000000 : ℝ)*X 2 1+(2115868753/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1186_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1463662787826396324625549869/186125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1552005283/100000000000000 : ℝ)*(base19) + (1434648257/100000000000000 : ℝ)*(base23) + (5884567/10000000000000 : ℝ)*(lower2) + (200615653/100000000000000 : ℝ)*(upper3) + (119625531/100000000000000 : ℝ)*(upper5) + (2907768391696611/50000000000000 : ℝ)*(major0) + (2907768391696611/50000000000000 : ℝ)*(major1) + (2907768391696611/50000000000000 : ℝ)*(major2) + (1940648257319289/25000000000000 : ℝ)*(sp0) + (1940658294556689/25000000000000 : ℝ)*(sp1) + (7762633295583781/100000000000000 : ℝ)*(sp2) + (1934208121709269/50000000000000 : ℝ)*(sp3) + (41700954883/100000000000000 : ℝ)*(sp4) + (11165503427/50000000000000 : ℝ)*(sp7) + (241777410901587/6250000000000 : ℝ)*(f.failure) + (3881317365116019/50000000000000 : ℝ)*(f.sum) + (4736913291553/3722500000000000000000000000 : ℝ)*base65 + (5504549803590408377/744500000000000000000000000000000 : ℝ)*base67 + (19312211762455408377/744500000000000000000000000000000 : ℝ)*base69 + (16185360581108091623/744500000000000000000000000000000 : ℝ)*base72 + (63562122604681/7445000000000000000000000000 : ℝ)*base73 + (31710118756209908377/744500000000000000000000000000000 : ℝ)*base75 + (7724212159551908377/744500000000000000000000000000000 : ℝ)*base77 + (15539343976645908377/744500000000000000000000000000000 : ℝ)*base79 + (425558426377/58164062500000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1548801/625000000000000000000 : ℝ)*base89 + (1548801/625000000000000000000 : ℝ)*base91 + (1548801/625000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5422016157628394227878364779/744500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (723818939/50000000000000 : ℝ)*(base19) + (1317185379/100000000000000 : ℝ)*(base23) + (12258643/10000000000000 : ℝ)*(upper3) + (9771449/25000000000000 : ℝ)*(lower4) + (76799087/50000000000000 : ℝ)*(upper5) + (5845650817217967/100000000000000 : ℝ)*(major0) + (5845650817217967/100000000000000 : ℝ)*(major1) + (5845650817217967/100000000000000 : ℝ)*(major2) + (20420506657/50000000000000 : ℝ)*(sp1) + (4134012597/10000000000000 : ℝ)*(sp2) + (3901415627244223/50000000000000 : ℝ)*(sp4) + (3901394482918627/50000000000000 : ℝ)*(sp5) + (975348574647137/12500000000000 : ℝ)*(sp6) + (972117534297189/25000000000000 : ℝ)*(sp7) + (972117534297189/25000000000000 : ℝ)*(f.failure) + (3901415627244223/50000000000000 : ℝ)*(f.sum) + (29254356848297/14890000000000000000000000000 : ℝ)*base65 + (2029574020579009469/1489000000000000000000000000000000 : ℝ)*base67 + (7049157060731009469/1489000000000000000000000000000000 : ℝ)*base69 + (15526147305137009469/1489000000000000000000000000000000 : ℝ)*base71 + (24463800255143/14890000000000000000000000000 : ℝ)*base74 + (984949432493009469/1489000000000000000000000000000000 : ℝ)*base75 + (9040604830613009469/1489000000000000000000000000000000 : ℝ)*base77 + (17270993276873009469/1489000000000000000000000000000000 : ℝ)*base79 + (31009940439777/14890000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (1946553/2500000000000000000000 : ℝ)*base90 + (1946553/2500000000000000000000 : ℝ)*base92 + (1946553/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1186_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4189/1024 : ℝ) ≤ p) (hpb : p ≤ (8379/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150332923/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7117/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1407/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5689/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14107/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1186_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1186_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4189/1024 : ℝ) ≤ p) (hpb : p ≤ (8379/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150332923/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (131/800 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1853/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5689/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14107/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1186_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1186_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1186_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4189/1024 : ℝ) ≤ p) (hpb : p ≤ (8379/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150332923/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (131/800 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1853/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5689/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14107/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1186_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
