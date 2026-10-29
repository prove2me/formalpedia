-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1480_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:12:38.261003+00:00
-- url     : https://prove2.me/submissions/a91babee-e924-4a38-a2c0-4126ac85af6f

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
theorem support_rectangle_w1480_s0_0 (p : ℝ) (hpa : (4455/1024 : ℝ) ≤ p) (hpb : p ≤ (4457/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-344061283/2000000000 : ℝ)*x 0 + (5937895849/10000000000 : ℝ)*x 1 + (4841393013/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (344061283/2000000000 : ℝ)^4457 ≤ (2544141476893/25000000000000 : ℝ)^3433 := by
    have hnat : (344061283 : ℕ)^4457*25000000000000^3433 ≤ 2544141476893^3433*2000000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      344061283 2000000000 2544141476893 25000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5937895849/10000000000 : ℝ)^4457 ≤ (25414489528263/50000000000000 : ℝ)^3433 := by
    have hnat : (5937895849 : ℕ)^4457*50000000000000^3433 ≤ 25414489528263^3433*10000000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5937895849 10000000000 25414489528263 50000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4841393013/10000000000 : ℝ)^4457 ≤ (38994455014047/100000000000000 : ℝ)^3433 := by
    have hnat : (4841393013 : ℕ)^4457*100000000000000^3433 ≤ 38994455014047^3433*10000000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4841393013 10000000000 38994455014047 100000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4457/1024 : ℝ)) 4457 3433 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-344061283/2000000000 : ℝ), (5937895849/10000000000 : ℝ), (4841393013/10000000000 : ℝ)] ![(2544141476893/25000000000000 : ℝ), (25414489528263/50000000000000 : ℝ), (38994455014047/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-344061283/2000000000 : ℝ)|^4457 ≤ (2544141476893/25000000000000 : ℝ)^3433
        have hw : |(-344061283/2000000000 : ℝ)|=(344061283/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5937895849/10000000000 : ℝ)|^4457 ≤ (25414489528263/50000000000000 : ℝ)^3433
        have hw : |(5937895849/10000000000 : ℝ)|=(5937895849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4841393013/10000000000 : ℝ)|^4457 ≤ (38994455014047/100000000000000 : ℝ)^3433
        have hw : |(4841393013/10000000000 : ℝ)|=(4841393013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1480_s0_1 (p : ℝ) (hpa : (4455/1024 : ℝ) ≤ p) (hpb : p ≤ (4457/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2742487853/5000000000 : ℝ)*x 0 + (-584375543/2500000000 : ℝ)*x 1 + (605174131/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2742487853/5000000000 : ℝ)^4457 ≤ (22926902445001/50000000000000 : ℝ)^3433 := by
    have hnat : (2742487853 : ℕ)^4457*50000000000000^3433 ≤ 22926902445001^3433*5000000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2742487853 5000000000 22926902445001 50000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (584375543/2500000000 : ℝ)^4457 ≤ (15151739718963/100000000000000 : ℝ)^3433 := by
    have hnat : (584375543 : ℕ)^4457*100000000000000^3433 ≤ 15151739718963^3433*2500000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      584375543 2500000000 15151739718963 100000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (605174131/1250000000 : ℝ)^4457 ≤ (38994455380037/100000000000000 : ℝ)^3433 := by
    have hnat : (605174131 : ℕ)^4457*100000000000000^3433 ≤ 38994455380037^3433*1250000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      605174131 1250000000 38994455380037 100000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4457/1024 : ℝ)) 4457 3433 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2742487853/5000000000 : ℝ), (-584375543/2500000000 : ℝ), (605174131/1250000000 : ℝ)] ![(22926902445001/50000000000000 : ℝ), (15151739718963/100000000000000 : ℝ), (38994455380037/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2742487853/5000000000 : ℝ)|^4457 ≤ (22926902445001/50000000000000 : ℝ)^3433
        have hw : |(2742487853/5000000000 : ℝ)|=(2742487853/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-584375543/2500000000 : ℝ)|^4457 ≤ (15151739718963/100000000000000 : ℝ)^3433
        have hw : |(-584375543/2500000000 : ℝ)|=(584375543/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(605174131/1250000000 : ℝ)|^4457 ≤ (38994455380037/100000000000000 : ℝ)^3433
        have hw : |(605174131/1250000000 : ℝ)|=(605174131/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1480_s0_2 (p : ℝ) (hpa : (4455/1024 : ℝ) ≤ p) (hpb : p ≤ (4457/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2742487813/5000000000 : ℝ)*x 0 + (968278617/2000000000 : ℝ)*x 1 + (-584375557/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2742487813/5000000000 : ℝ)^4457 ≤ (45853804021723/100000000000000 : ℝ)^3433 := by
    have hnat : (2742487813 : ℕ)^4457*100000000000000^3433 ≤ 45853804021723^3433*5000000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2742487813 5000000000 45853804021723 100000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (968278617/2000000000 : ℝ)^4457 ≤ (38994455766941/100000000000000 : ℝ)^3433 := by
    have hnat : (968278617 : ℕ)^4457*100000000000000^3433 ≤ 38994455766941^3433*2000000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      968278617 2000000000 38994455766941 100000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (584375557/2500000000 : ℝ)^4457 ≤ (1515174019023/10000000000000 : ℝ)^3433 := by
    have hnat : (584375557 : ℕ)^4457*10000000000000^3433 ≤ 1515174019023^3433*2500000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      584375557 2500000000 1515174019023 10000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4457/1024 : ℝ)) 4457 3433 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2742487813/5000000000 : ℝ), (968278617/2000000000 : ℝ), (-584375557/2500000000 : ℝ)] ![(45853804021723/100000000000000 : ℝ), (38994455766941/100000000000000 : ℝ), (1515174019023/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2742487813/5000000000 : ℝ)|^4457 ≤ (45853804021723/100000000000000 : ℝ)^3433
        have hw : |(2742487813/5000000000 : ℝ)|=(2742487813/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(968278617/2000000000 : ℝ)|^4457 ≤ (38994455766941/100000000000000 : ℝ)^3433
        have hw : |(968278617/2000000000 : ℝ)|=(968278617/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-584375557/2500000000 : ℝ)|^4457 ≤ (1515174019023/10000000000000 : ℝ)^3433
        have hw : |(-584375557/2500000000 : ℝ)|=(584375557/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1480_s0_3 (p : ℝ) (hpa : (4455/1024 : ℝ) ≤ p) (hpb : p ≤ (4457/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2076943561/5000000000 : ℝ)*x 0 + (3091479759/10000000000 : ℝ)*x 1 + (2760966073/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2076943561/5000000000 : ℝ)^4457 ≤ (31962947905187/100000000000000 : ℝ)^3433 := by
    have hnat : (2076943561 : ℕ)^4457*100000000000000^3433 ≤ 31962947905187^3433*5000000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2076943561 5000000000 31962947905187 100000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3091479759/10000000000 : ℝ)^4457 ≤ (871269533221/4000000000000 : ℝ)^3433 := by
    have hnat : (3091479759 : ℕ)^4457*4000000000000^3433 ≤ 871269533221^3433*10000000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3091479759 10000000000 871269533221 4000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2760966073/5000000000 : ℝ)^4457 ≤ (23127656876809/50000000000000 : ℝ)^3433 := by
    have hnat : (2760966073 : ℕ)^4457*50000000000000^3433 ≤ 23127656876809^3433*5000000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2760966073 5000000000 23127656876809 50000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4457/1024 : ℝ)) 4457 3433 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2076943561/5000000000 : ℝ), (3091479759/10000000000 : ℝ), (2760966073/5000000000 : ℝ)] ![(31962947905187/100000000000000 : ℝ), (871269533221/4000000000000 : ℝ), (23127656876809/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2076943561/5000000000 : ℝ)|^4457 ≤ (31962947905187/100000000000000 : ℝ)^3433
        have hw : |(2076943561/5000000000 : ℝ)|=(2076943561/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3091479759/10000000000 : ℝ)|^4457 ≤ (871269533221/4000000000000 : ℝ)^3433
        have hw : |(3091479759/10000000000 : ℝ)|=(3091479759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2760966073/5000000000 : ℝ)|^4457 ≤ (23127656876809/50000000000000 : ℝ)^3433
        have hw : |(2760966073/5000000000 : ℝ)|=(2760966073/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1480_s0_4 (p : ℝ) (hpa : (4455/1024 : ℝ) ≤ p) (hpb : p ≤ (4457/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-862054923/5000000000 : ℝ)*x 0 + (2434761603/5000000000 : ℝ)*x 1 + (5908753997/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (862054923/5000000000 : ℝ)^4457 ≤ (5102893044837/50000000000000 : ℝ)^3433 := by
    have hnat : (862054923 : ℕ)^4457*50000000000000^3433 ≤ 5102893044837^3433*5000000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      862054923 5000000000 5102893044837 50000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2434761603/5000000000 : ℝ)^4457 ≤ (1571554523839/4000000000000 : ℝ)^3433 := by
    have hnat : (2434761603 : ℕ)^4457*4000000000000^3433 ≤ 1571554523839^3433*5000000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2434761603 5000000000 1571554523839 4000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5908753997/10000000000 : ℝ)^4457 ≤ (50505350805599/100000000000000 : ℝ)^3433 := by
    have hnat : (5908753997 : ℕ)^4457*100000000000000^3433 ≤ 50505350805599^3433*10000000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5908753997 10000000000 50505350805599 100000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4457/1024 : ℝ)) 4457 3433 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-862054923/5000000000 : ℝ), (2434761603/5000000000 : ℝ), (5908753997/10000000000 : ℝ)] ![(5102893044837/50000000000000 : ℝ), (1571554523839/4000000000000 : ℝ), (50505350805599/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-862054923/5000000000 : ℝ)|^4457 ≤ (5102893044837/50000000000000 : ℝ)^3433
        have hw : |(-862054923/5000000000 : ℝ)|=(862054923/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2434761603/5000000000 : ℝ)|^4457 ≤ (1571554523839/4000000000000 : ℝ)^3433
        have hw : |(2434761603/5000000000 : ℝ)|=(2434761603/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5908753997/10000000000 : ℝ)|^4457 ≤ (50505350805599/100000000000000 : ℝ)^3433
        have hw : |(5908753997/10000000000 : ℝ)|=(5908753997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1480_s0_5 (p : ℝ) (hpa : (4455/1024 : ℝ) ≤ p) (hpb : p ≤ (4457/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5185580207/10000000000 : ℝ)*x 0 + (-254028203/2000000000 : ℝ)*x 1 + (590875399/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5185580207/10000000000 : ℝ)^4457 ≤ (42631117388347/100000000000000 : ℝ)^3433 := by
    have hnat : (5185580207 : ℕ)^4457*100000000000000^3433 ≤ 42631117388347^3433*10000000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5185580207 10000000000 42631117388347 100000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (254028203/2000000000 : ℝ)^4457 ≤ (1715882967337/25000000000000 : ℝ)^3433 := by
    have hnat : (254028203 : ℕ)^4457*25000000000000^3433 ≤ 1715882967337^3433*2000000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      254028203 2000000000 1715882967337 25000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (590875399/1000000000 : ℝ)^4457 ≤ (50505350727919/100000000000000 : ℝ)^3433 := by
    have hnat : (590875399 : ℕ)^4457*100000000000000^3433 ≤ 50505350727919^3433*1000000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      590875399 1000000000 50505350727919 100000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4457/1024 : ℝ)) 4457 3433 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5185580207/10000000000 : ℝ), (-254028203/2000000000 : ℝ), (590875399/1000000000 : ℝ)] ![(42631117388347/100000000000000 : ℝ), (1715882967337/25000000000000 : ℝ), (50505350727919/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5185580207/10000000000 : ℝ)|^4457 ≤ (42631117388347/100000000000000 : ℝ)^3433
        have hw : |(5185580207/10000000000 : ℝ)|=(5185580207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-254028203/2000000000 : ℝ)|^4457 ≤ (1715882967337/25000000000000 : ℝ)^3433
        have hw : |(-254028203/2000000000 : ℝ)|=(254028203/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(590875399/1000000000 : ℝ)|^4457 ≤ (50505350727919/100000000000000 : ℝ)^3433
        have hw : |(590875399/1000000000 : ℝ)|=(590875399/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1480_s0_6 (p : ℝ) (hpa : (4455/1024 : ℝ) ≤ p) (hpb : p ≤ (4457/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2592790049/5000000000 : ℝ)*x 0 + (1477188493/2500000000 : ℝ)*x 1 + (-127014121/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2592790049/5000000000 : ℝ)^4457 ≤ (21315558112479/50000000000000 : ℝ)^3433 := by
    have hnat : (2592790049 : ℕ)^4457*50000000000000^3433 ≤ 21315558112479^3433*5000000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2592790049 5000000000 21315558112479 50000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1477188493/2500000000 : ℝ)^4457 ≤ (50505350528171/100000000000000 : ℝ)^3433 := by
    have hnat : (1477188493 : ℕ)^4457*100000000000000^3433 ≤ 50505350528171^3433*2500000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1477188493 2500000000 50505350528171 100000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (127014121/1000000000 : ℝ)^4457 ≤ (686353323739/10000000000000 : ℝ)^3433 := by
    have hnat : (127014121 : ℕ)^4457*10000000000000^3433 ≤ 686353323739^3433*1000000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      127014121 1000000000 686353323739 10000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4457/1024 : ℝ)) 4457 3433 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2592790049/5000000000 : ℝ), (1477188493/2500000000 : ℝ), (-127014121/1000000000 : ℝ)] ![(21315558112479/50000000000000 : ℝ), (50505350528171/100000000000000 : ℝ), (686353323739/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2592790049/5000000000 : ℝ)|^4457 ≤ (21315558112479/50000000000000 : ℝ)^3433
        have hw : |(2592790049/5000000000 : ℝ)|=(2592790049/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1477188493/2500000000 : ℝ)|^4457 ≤ (50505350528171/100000000000000 : ℝ)^3433
        have hw : |(1477188493/2500000000 : ℝ)|=(1477188493/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-127014121/1000000000 : ℝ)|^4457 ≤ (686353323739/10000000000000 : ℝ)^3433
        have hw : |(-127014121/1000000000 : ℝ)|=(127014121/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1480_s0_7 (p : ℝ) (hpa : (4455/1024 : ℝ) ≤ p) (hpb : p ≤ (4457/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (41623181/100000000 : ℝ)*x 0 + (1091915999/2000000000 : ℝ)*x 1 + (3156074261/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (41623181/100000000 : ℝ)^4457 ≤ (16023598990823/50000000000000 : ℝ)^3433 := by
    have hnat : (41623181 : ℕ)^4457*50000000000000^3433 ≤ 16023598990823^3433*100000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41623181 100000000 16023598990823 50000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1091915999/2000000000 : ℝ)^4457 ≤ (72925381241/160000000000 : ℝ)^3433 := by
    have hnat : (1091915999 : ℕ)^4457*160000000000^3433 ≤ 72925381241^3433*2000000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1091915999 2000000000 72925381241 160000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3156074261/10000000000 : ℝ)^4457 ≤ (4474887746671/20000000000000 : ℝ)^3433 := by
    have hnat : (3156074261 : ℕ)^4457*20000000000000^3433 ≤ 4474887746671^3433*10000000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3156074261 10000000000 4474887746671 20000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4457/1024 : ℝ)) 4457 3433 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(41623181/100000000 : ℝ), (1091915999/2000000000 : ℝ), (3156074261/10000000000 : ℝ)] ![(16023598990823/50000000000000 : ℝ), (72925381241/160000000000 : ℝ), (4474887746671/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(41623181/100000000 : ℝ)|^4457 ≤ (16023598990823/50000000000000 : ℝ)^3433
        have hw : |(41623181/100000000 : ℝ)|=(41623181/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1091915999/2000000000 : ℝ)|^4457 ≤ (72925381241/160000000000 : ℝ)^3433
        have hw : |(1091915999/2000000000 : ℝ)|=(1091915999/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3156074261/10000000000 : ℝ)|^4457 ≤ (4474887746671/20000000000000 : ℝ)^3433
        have hw : |(3156074261/10000000000 : ℝ)|=(3156074261/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1480_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4455/1024 : ℝ) ≤ p) (hpb : p ≤ (4457/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (40206863/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (1203/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (5181/20000 : ℝ)*pair X 0 0 := by
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
  have base32 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1+(1 : ℝ)*X 2 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 1).2]
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
  have hpowlo : (0 : ℝ) ^ (4455/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4455 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4455*1^1024 ≤ 0^1024*1^4455 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4455 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4455 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4455/1024 : ℝ) ≤ (371328078247715557/20000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4455 ≤ (371328078247715557/20000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4455*20000000000000000000^1024 ≤ 371328078247715557^1024*5^4455 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 371328078247715557 20000000000000000000 4455 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (371328078247715557/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4455 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4455/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4455 := by
      have hnat : (1 : ℕ)^1024*1^4455 ≤ 1^4455*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4455 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4455 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20371328078247715557/20000000000000000000 : ℝ) ≤ (10042373833974759/10000000000000000 : ℝ) ^ (4455/1024 : ℝ) := by
    have hpowers : (20371328078247715557/20000000000000000000 : ℝ)^1024 ≤ (10042373833974759/10000000000000000 : ℝ)^4455 := by
      have hnat : (20371328078247715557 : ℕ)^1024*10000000000000000^4455 ≤ 10042373833974759^4455*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20371328078247715557 20000000000000000000 10042373833974759 10000000000000000 1024 4455 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10042373833974759/10000000000000000 : ℝ)) (X := (20371328078247715557/20000000000000000000 : ℝ)) (by norm_num) 4455 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10371328078247715557/10000000000000000000 : ℝ) ≤ (5042373833974759/5000000000000000 : ℝ) ^ (4455/1024 : ℝ) := by
    have hpowers : (10371328078247715557/10000000000000000000 : ℝ)^1024 ≤ (5042373833974759/5000000000000000 : ℝ)^4455 := by
      have hnat : (10371328078247715557 : ℕ)^1024*5000000000000000^4455 ≤ 5042373833974759^4455*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10371328078247715557 10000000000000000000 5042373833974759 5000000000000000 1024 4455 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5042373833974759/5000000000000000 : ℝ)) (X := (10371328078247715557/10000000000000000000 : ℝ)) (by norm_num) 4455 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(42373833974759/4000000000000000 : ℝ)*(0 : ℝ))^(4455/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(42373833974759/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(371328078247715557/20000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(42373833974759/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4455/1024 : ℝ) := by
    rw [show (1 : ℝ)+(42373833974759/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10042373833974759/10000000000000000 : ℝ) by norm_num, show 1+(371328078247715557/20000000000000000000 : ℝ)+(0 : ℝ)=(20371328078247715557/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(371328078247715557/20000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(42373833974759/4000000000000000 : ℝ)*(2/5 : ℝ))^(4455/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(42373833974759/4000000000000000 : ℝ)*(2/5 : ℝ)=(5042373833974759/5000000000000000 : ℝ) by norm_num, show 1+2*(371328078247715557/20000000000000000000 : ℝ)=(10371328078247715557/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(42373833974759/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4455/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (42373833974759/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(42373833974759/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4455/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (42373833974759/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(42373833974759/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4455/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (42373833974759/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-344061283/2000000000 : ℝ)*X 0 0+(5937895849/10000000000 : ℝ)*X 0 1+(4841393013/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1480_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2742487853/5000000000 : ℝ)*X 1 0+(-584375543/2500000000 : ℝ)*X 1 1+(605174131/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1480_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2742487813/5000000000 : ℝ)*X 2 0+(968278617/2000000000 : ℝ)*X 2 1+(-584375557/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1480_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2076943561/5000000000 : ℝ)*X 0 0+(3091479759/10000000000 : ℝ)*X 0 1+(2760966073/5000000000 : ℝ)*X 0 2+(2076943561/5000000000 : ℝ)*X 1 0+(3091479759/10000000000 : ℝ)*X 1 1+(2760966073/5000000000 : ℝ)*X 1 2+(2076943561/5000000000 : ℝ)*X 2 0+(3091479759/10000000000 : ℝ)*X 2 1+(2760966073/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1480_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-862054923/5000000000 : ℝ)*X 0 0+(2434761603/5000000000 : ℝ)*X 0 1+(5908753997/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1480_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5185580207/10000000000 : ℝ)*X 1 0+(-254028203/2000000000 : ℝ)*X 1 1+(590875399/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1480_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2592790049/5000000000 : ℝ)*X 2 0+(1477188493/2500000000 : ℝ)*X 2 1+(-127014121/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1480_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((41623181/100000000 : ℝ)*X 0 0+(1091915999/2000000000 : ℝ)*X 0 1+(3156074261/10000000000 : ℝ)*X 0 2+(41623181/100000000 : ℝ)*X 1 0+(1091915999/2000000000 : ℝ)*X 1 1+(3156074261/10000000000 : ℝ)*X 1 2+(41623181/100000000 : ℝ)*X 2 0+(1091915999/2000000000 : ℝ)*X 2 1+(3156074261/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1480_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (164555688924461957007957/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (18357701/100000000000000 : ℝ)*(base1) + (145322673/20000000000000 : ℝ)*(base19) + (178327913/25000000000000 : ℝ)*(base23) + (101662103/100000000000000 : ℝ)*(upper3) + (20538901/25000000000000 : ℝ)*(upper5) + (661721911016159/100000000000000 : ℝ)*(major0) + (661721911016159/100000000000000 : ℝ)*(major1) + (661721911016159/100000000000000 : ℝ)*(major2) + (227998216603069/25000000000000 : ℝ)*(sp0) + (911994627373841/100000000000000 : ℝ)*(sp1) + (455997320337777/50000000000000 : ℝ)*(sp2) + (25715445823973/6250000000000 : ℝ)*(sp3) + (313241579/12500000000000 : ℝ)*(sp4) + (30170001/2500000000000 : ℝ)*(sp7) + (41144835834131/10000000000000 : ℝ)*(f.failure) + (455997676993603/50000000000000 : ℝ)*(f.sum) + (796329630330681/200000000000000000000000000000 : ℝ)*base65 + (2397107475930681/400000000000000000000000000000 : ℝ)*base67 + (241025623130681/400000000000000000000000000000 : ℝ)*base69 + (2164090830330681/400000000000000000000000000000 : ℝ)*base71 + (958204195130681/200000000000000000000000000000 : ℝ)*base73 + (2893865752730681/400000000000000000000000000000 : ℝ)*base75 + (1604434807130681/400000000000000000000000000000 : ℝ)*base77 + (3403330046330681/400000000000000000000000000000 : ℝ)*base79 + (25134964069319/200000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1658947/250000000000000000000 : ℝ)*base90 + (1658947/250000000000000000000 : ℝ)*base92 + (1658947/250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (294586627410708216632739/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1352894591/100000000000000 : ℝ)*(base19) + (1335512421/100000000000000 : ℝ)*(base23) + (11144009/10000000000000 : ℝ)*(base32) + (48783777/25000000000000 : ℝ)*(upper3) + (63958557/50000000000000 : ℝ)*(upper5) + (174546320425469/25000000000000 : ℝ)*(major0) + (174546320425469/25000000000000 : ℝ)*(major1) + (174546320425469/25000000000000 : ℝ)*(major2) + (1675598963/50000000000000 : ℝ)*(sp1) + (212528643/6250000000000 : ℝ)*(sp2) + (481124826888271/50000000000000 : ℝ)*(sp4) + (120280618710503/12500000000000 : ℝ)*(sp5) + (962244917805833/100000000000000 : ℝ)*(sp6) + (434120601796029/100000000000000 : ℝ)*(sp7) + (434120713236119/100000000000000 : ℝ)*(f.failure) + (481124826888271/50000000000000 : ℝ)*(f.sum) + (65664668336971/50000000000000000000000000000 : ℝ)*base65 + (671523063963029/100000000000000000000000000000 : ℝ)*base68 + (1109520507563029/100000000000000000000000000000 : ℝ)*base70 + (78988075663029/100000000000000000000000000000 : ℝ)*base72 + (90860724413029/50000000000000000000000000000 : ℝ)*base74 + (13445909036971/100000000000000000000000000000 : ℝ)*base75 + (526658195463029/100000000000000000000000000000 : ℝ)*base78 + (1052545414363029/100000000000000000000000000000 : ℝ)*base80 + (181204012013029/50000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (23284697/2500000000000000000000 : ℝ)*base89 + (23284697/2500000000000000000000 : ℝ)*base91 + (23284697/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1480_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4455/1024 : ℝ) ≤ p) (hpb : p ≤ (4457/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (40206863/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1203/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (5181/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1480_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1480_s1_0 (p : ℝ) (hpa : (4455/1024 : ℝ) ≤ p) (hpb : p ≤ (4457/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-235338993/1250000000 : ℝ)*x 0 + (5592737793/10000000000 : ℝ)*x 1 + (1016461571/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (235338993/1250000000 : ℝ)^4457 ≤ (11441037453681/100000000000000 : ℝ)^3433 := by
    have hnat : (235338993 : ℕ)^4457*100000000000000^3433 ≤ 11441037453681^3433*1250000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      235338993 1250000000 11441037453681 100000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5592737793/10000000000 : ℝ)^4457 ≤ (47026811318411/100000000000000 : ℝ)^3433 := by
    have hnat : (5592737793 : ℕ)^4457*100000000000000^3433 ≤ 47026811318411^3433*10000000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5592737793 10000000000 47026811318411 100000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1016461571/2000000000 : ℝ)^4457 ≤ (4153215120801/10000000000000 : ℝ)^3433 := by
    have hnat : (1016461571 : ℕ)^4457*10000000000000^3433 ≤ 4153215120801^3433*2000000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1016461571 2000000000 4153215120801 10000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4457/1024 : ℝ)) 4457 3433 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-235338993/1250000000 : ℝ), (5592737793/10000000000 : ℝ), (1016461571/2000000000 : ℝ)] ![(11441037453681/100000000000000 : ℝ), (47026811318411/100000000000000 : ℝ), (4153215120801/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-235338993/1250000000 : ℝ)|^4457 ≤ (11441037453681/100000000000000 : ℝ)^3433
        have hw : |(-235338993/1250000000 : ℝ)|=(235338993/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5592737793/10000000000 : ℝ)|^4457 ≤ (47026811318411/100000000000000 : ℝ)^3433
        have hw : |(5592737793/10000000000 : ℝ)|=(5592737793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1016461571/2000000000 : ℝ)|^4457 ≤ (4153215120801/10000000000000 : ℝ)^3433
        have hw : |(1016461571/2000000000 : ℝ)|=(1016461571/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1480_s1_1 (p : ℝ) (hpa : (4455/1024 : ℝ) ≤ p) (hpb : p ≤ (4457/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2696281897/5000000000 : ℝ)*x 0 + (-1076305797/5000000000 : ℝ)*x 1 + (2541154109/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2696281897/5000000000 : ℝ)^4457 ≤ (44853343190807/100000000000000 : ℝ)^3433 := by
    have hnat : (2696281897 : ℕ)^4457*100000000000000^3433 ≤ 44853343190807^3433*5000000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696281897 5000000000 44853343190807 100000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1076305797/5000000000 : ℝ)^4457 ≤ (850906358709/6250000000000 : ℝ)^3433 := by
    have hnat : (1076305797 : ℕ)^4457*6250000000000^3433 ≤ 850906358709^3433*5000000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1076305797 5000000000 850906358709 6250000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2541154109/5000000000 : ℝ)^4457 ≤ (8306431011847/20000000000000 : ℝ)^3433 := by
    have hnat : (2541154109 : ℕ)^4457*20000000000000^3433 ≤ 8306431011847^3433*5000000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2541154109 5000000000 8306431011847 20000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4457/1024 : ℝ)) 4457 3433 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2696281897/5000000000 : ℝ), (-1076305797/5000000000 : ℝ), (2541154109/5000000000 : ℝ)] ![(44853343190807/100000000000000 : ℝ), (850906358709/6250000000000 : ℝ), (8306431011847/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2696281897/5000000000 : ℝ)|^4457 ≤ (44853343190807/100000000000000 : ℝ)^3433
        have hw : |(2696281897/5000000000 : ℝ)|=(2696281897/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1076305797/5000000000 : ℝ)|^4457 ≤ (850906358709/6250000000000 : ℝ)^3433
        have hw : |(-1076305797/5000000000 : ℝ)|=(1076305797/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2541154109/5000000000 : ℝ)|^4457 ≤ (8306431011847/20000000000000 : ℝ)^3433
        have hw : |(2541154109/5000000000 : ℝ)|=(2541154109/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1480_s1_2 (p : ℝ) (hpa : (4455/1024 : ℝ) ≤ p) (hpb : p ≤ (4457/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5392564251/10000000000 : ℝ)*x 0 + (158822123/312500000 : ℝ)*x 1 + (-2152611357/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5392564251/10000000000 : ℝ)^4457 ≤ (22426674062889/50000000000000 : ℝ)^3433 := by
    have hnat : (5392564251 : ℕ)^4457*50000000000000^3433 ≤ 22426674062889^3433*10000000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392564251 10000000000 22426674062889 50000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (158822123/312500000 : ℝ)^4457 ≤ (20766076033687/50000000000000 : ℝ)^3433 := by
    have hnat : (158822123 : ℕ)^4457*50000000000000^3433 ≤ 20766076033687^3433*312500000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      158822123 312500000 20766076033687 50000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2152611357/10000000000 : ℝ)^4457 ≤ (6807249896649/50000000000000 : ℝ)^3433 := by
    have hnat : (2152611357 : ℕ)^4457*50000000000000^3433 ≤ 6807249896649^3433*10000000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2152611357 10000000000 6807249896649 50000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4457/1024 : ℝ)) 4457 3433 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5392564251/10000000000 : ℝ), (158822123/312500000 : ℝ), (-2152611357/10000000000 : ℝ)] ![(22426674062889/50000000000000 : ℝ), (20766076033687/50000000000000 : ℝ), (6807249896649/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5392564251/10000000000 : ℝ)|^4457 ≤ (22426674062889/50000000000000 : ℝ)^3433
        have hw : |(5392564251/10000000000 : ℝ)|=(5392564251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(158822123/312500000 : ℝ)|^4457 ≤ (20766076033687/50000000000000 : ℝ)^3433
        have hw : |(158822123/312500000 : ℝ)|=(158822123/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2152611357/10000000000 : ℝ)|^4457 ≤ (6807249896649/50000000000000 : ℝ)^3433
        have hw : |(-2152611357/10000000000 : ℝ)|=(2152611357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1480_s1_3 (p : ℝ) (hpa : (4455/1024 : ℝ) ≤ p) (hpb : p ≤ (4457/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4261265627/10000000000 : ℝ)*x 0 + (3728118739/10000000000 : ℝ)*x 1 + (4859511567/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4261265627/10000000000 : ℝ)^4457 ≤ (33039758854417/100000000000000 : ℝ)^3433 := by
    have hnat : (4261265627 : ℕ)^4457*100000000000000^3433 ≤ 33039758854417^3433*10000000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4261265627 10000000000 33039758854417 100000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3728118739/10000000000 : ℝ)^4457 ≤ (27776217249051/100000000000000 : ℝ)^3433 := by
    have hnat : (3728118739 : ℕ)^4457*100000000000000^3433 ≤ 27776217249051^3433*10000000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3728118739 10000000000 27776217249051 100000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4859511567/10000000000 : ℝ)^4457 ≤ (19592011937921/50000000000000 : ℝ)^3433 := by
    have hnat : (4859511567 : ℕ)^4457*50000000000000^3433 ≤ 19592011937921^3433*10000000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4859511567 10000000000 19592011937921 50000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4457/1024 : ℝ)) 4457 3433 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4261265627/10000000000 : ℝ), (3728118739/10000000000 : ℝ), (4859511567/10000000000 : ℝ)] ![(33039758854417/100000000000000 : ℝ), (27776217249051/100000000000000 : ℝ), (19592011937921/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4261265627/10000000000 : ℝ)|^4457 ≤ (33039758854417/100000000000000 : ℝ)^3433
        have hw : |(4261265627/10000000000 : ℝ)|=(4261265627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3728118739/10000000000 : ℝ)|^4457 ≤ (27776217249051/100000000000000 : ℝ)^3433
        have hw : |(3728118739/10000000000 : ℝ)|=(3728118739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4859511567/10000000000 : ℝ)|^4457 ≤ (19592011937921/50000000000000 : ℝ)^3433
        have hw : |(4859511567/10000000000 : ℝ)|=(4859511567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1480_s1_4 (p : ℝ) (hpa : (4455/1024 : ℝ) ≤ p) (hpb : p ≤ (4457/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-235385157/1250000000 : ℝ)*x 0 + (254414019/500000000 : ℝ)*x 1 + (139666611/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (235385157/1250000000 : ℝ)^4457 ≤ (2288790246369/20000000000000 : ℝ)^3433 := by
    have hnat : (235385157 : ℕ)^4457*20000000000000^3433 ≤ 2288790246369^3433*1250000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      235385157 1250000000 2288790246369 20000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (254414019/500000000 : ℝ)^4457 ≤ (41595527431091/100000000000000 : ℝ)^3433 := by
    have hnat : (254414019 : ℕ)^4457*100000000000000^3433 ≤ 41595527431091^3433*500000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      254414019 500000000 41595527431091 100000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (139666611/250000000 : ℝ)^4457 ≤ (9392104262193/20000000000000 : ℝ)^3433 := by
    have hnat : (139666611 : ℕ)^4457*20000000000000^3433 ≤ 9392104262193^3433*250000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      139666611 250000000 9392104262193 20000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4457/1024 : ℝ)) 4457 3433 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-235385157/1250000000 : ℝ), (254414019/500000000 : ℝ), (139666611/250000000 : ℝ)] ![(2288790246369/20000000000000 : ℝ), (41595527431091/100000000000000 : ℝ), (9392104262193/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-235385157/1250000000 : ℝ)|^4457 ≤ (2288790246369/20000000000000 : ℝ)^3433
        have hw : |(-235385157/1250000000 : ℝ)|=(235385157/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(254414019/500000000 : ℝ)|^4457 ≤ (41595527431091/100000000000000 : ℝ)^3433
        have hw : |(254414019/500000000 : ℝ)|=(254414019/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(139666611/250000000 : ℝ)|^4457 ≤ (9392104262193/20000000000000 : ℝ)^3433
        have hw : |(139666611/250000000 : ℝ)|=(139666611/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1480_s1_5 (p : ℝ) (hpa : (4455/1024 : ℝ) ≤ p) (hpb : p ≤ (4457/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1314665629/2500000000 : ℝ)*x 0 + (-51507969/312500000 : ℝ)*x 1 + (34916653/62500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1314665629/2500000000 : ℝ)^4457 ≤ (21706390008893/50000000000000 : ℝ)^3433 := by
    have hnat : (1314665629 : ℕ)^4457*50000000000000^3433 ≤ 21706390008893^3433*2500000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1314665629 2500000000 21706390008893 50000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (51507969/312500000 : ℝ)^4457 ≤ (9626698217451/100000000000000 : ℝ)^3433 := by
    have hnat : (51507969 : ℕ)^4457*100000000000000^3433 ≤ 9626698217451^3433*312500000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      51507969 312500000 9626698217451 100000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (34916653/62500000 : ℝ)^4457 ≤ (4696052174749/10000000000000 : ℝ)^3433 := by
    have hnat : (34916653 : ℕ)^4457*10000000000000^3433 ≤ 4696052174749^3433*62500000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      34916653 62500000 4696052174749 10000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4457/1024 : ℝ)) 4457 3433 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1314665629/2500000000 : ℝ), (-51507969/312500000 : ℝ), (34916653/62500000 : ℝ)] ![(21706390008893/50000000000000 : ℝ), (9626698217451/100000000000000 : ℝ), (4696052174749/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1314665629/2500000000 : ℝ)|^4457 ≤ (21706390008893/50000000000000 : ℝ)^3433
        have hw : |(1314665629/2500000000 : ℝ)|=(1314665629/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-51507969/312500000 : ℝ)|^4457 ≤ (9626698217451/100000000000000 : ℝ)^3433
        have hw : |(-51507969/312500000 : ℝ)|=(51507969/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(34916653/62500000 : ℝ)|^4457 ≤ (4696052174749/10000000000000 : ℝ)^3433
        have hw : |(34916653/62500000 : ℝ)|=(34916653/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1480_s1_6 (p : ℝ) (hpa : (4455/1024 : ℝ) ≤ p) (hpb : p ≤ (4457/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5258662539/10000000000 : ℝ)*x 0 + (111733289/200000000 : ℝ)*x 1 + (-1648255019/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5258662539/10000000000 : ℝ)^4457 ≤ (21706390132149/50000000000000 : ℝ)^3433 := by
    have hnat : (5258662539 : ℕ)^4457*50000000000000^3433 ≤ 21706390132149^3433*10000000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5258662539 10000000000 21706390132149 50000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (111733289/200000000 : ℝ)^4457 ≤ (46960521420097/100000000000000 : ℝ)^3433 := by
    have hnat : (111733289 : ℕ)^4457*100000000000000^3433 ≤ 46960521420097^3433*200000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      111733289 200000000 46960521420097 100000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1648255019/10000000000 : ℝ)^4457 ≤ (9626698300861/100000000000000 : ℝ)^3433 := by
    have hnat : (1648255019 : ℕ)^4457*100000000000000^3433 ≤ 9626698300861^3433*10000000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1648255019 10000000000 9626698300861 100000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4457/1024 : ℝ)) 4457 3433 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5258662539/10000000000 : ℝ), (111733289/200000000 : ℝ), (-1648255019/10000000000 : ℝ)] ![(21706390132149/50000000000000 : ℝ), (46960521420097/100000000000000 : ℝ), (9626698300861/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5258662539/10000000000 : ℝ)|^4457 ≤ (21706390132149/50000000000000 : ℝ)^3433
        have hw : |(5258662539/10000000000 : ℝ)|=(5258662539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(111733289/200000000 : ℝ)|^4457 ≤ (46960521420097/100000000000000 : ℝ)^3433
        have hw : |(111733289/200000000 : ℝ)|=(111733289/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1648255019/10000000000 : ℝ)|^4457 ≤ (9626698300861/100000000000000 : ℝ)^3433
        have hw : |(-1648255019/10000000000 : ℝ)|=(1648255019/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1480_s1_7 (p : ℝ) (hpa : (4455/1024 : ℝ) ≤ p) (hpb : p ≤ (4457/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (852416871/2000000000 : ℝ)*x 0 + (4846273681/10000000000 : ℝ)*x 1 + (7483161/20000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (852416871/2000000000 : ℝ)^4457 ≤ (1652400029977/5000000000000 : ℝ)^3433 := by
    have hnat : (852416871 : ℕ)^4457*5000000000000^3433 ≤ 1652400029977^3433*2000000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      852416871 2000000000 1652400029977 5000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4846273681/10000000000 : ℝ)^4457 ≤ (19522749576907/50000000000000 : ℝ)^3433 := by
    have hnat : (4846273681 : ℕ)^4457*50000000000000^3433 ≤ 19522749576907^3433*10000000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4846273681 10000000000 19522749576907 50000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7483161/20000000 : ℝ)^4457 ≤ (27906500231063/100000000000000 : ℝ)^3433 := by
    have hnat : (7483161 : ℕ)^4457*100000000000000^3433 ≤ 27906500231063^3433*20000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7483161 20000000 27906500231063 100000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4457/1024 : ℝ)) 4457 3433 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(852416871/2000000000 : ℝ), (4846273681/10000000000 : ℝ), (7483161/20000000 : ℝ)] ![(1652400029977/5000000000000 : ℝ), (19522749576907/50000000000000 : ℝ), (27906500231063/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(852416871/2000000000 : ℝ)|^4457 ≤ (1652400029977/5000000000000 : ℝ)^3433
        have hw : |(852416871/2000000000 : ℝ)|=(852416871/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4846273681/10000000000 : ℝ)|^4457 ≤ (19522749576907/50000000000000 : ℝ)^3433
        have hw : |(4846273681/10000000000 : ℝ)|=(4846273681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(7483161/20000000 : ℝ)|^4457 ≤ (27906500231063/100000000000000 : ℝ)^3433
        have hw : |(7483161/20000000 : ℝ)|=(7483161/20000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1480_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4455/1024 : ℝ) ≤ p) (hpb : p ≤ (4457/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (40206863/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (5181/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1203/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (3953/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2337/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (5181/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1203/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (5181/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1203/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (5181/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1203/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (5181/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1203/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (5181/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1203/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (5181/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1203/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1203/50000 : ℝ) ^ (4455/1024 : ℝ) ≤ (9071675367421/100000000000000000000 : ℝ) := by
    have hpowers : (1203/50000 : ℝ)^4455 ≤ (9071675367421/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1203 : ℕ)^4455*100000000000000000000^1024 ≤ 9071675367421^1024*50000^4455 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1203 50000 9071675367421 100000000000000000000 4455 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1203/50000 : ℝ)) (X := (9071675367421/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4455 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (5181/20000 : ℝ) ^ (4455/1024 : ℝ) ≤ (56092515991107891/20000000000000000000 : ℝ) := by
    have hpowers : (5181/20000 : ℝ)^4455 ≤ (56092515991107891/20000000000000000000 : ℝ)^1024 := by
      have hnat : (5181 : ℕ)^4455*20000000000000000000^1024 ≤ 56092515991107891^1024*20000^4455 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5181 20000 56092515991107891 20000000000000000000 4455 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5181/20000 : ℝ)) (X := (56092515991107891/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4455 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000009071675367421/50000000000000000000 : ℝ) ≤ (15625000651613/15625000000000 : ℝ) ^ (4455/1024 : ℝ) := by
    have hpowers : (50000009071675367421/50000000000000000000 : ℝ)^1024 ≤ (15625000651613/15625000000000 : ℝ)^4455 := by
      have hnat : (50000009071675367421 : ℕ)^1024*15625000000000^4455 ≤ 15625000651613^4455*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000009071675367421 50000000000000000000 15625000651613 15625000000000 1024 4455 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (15625000651613/15625000000000 : ℝ)) (X := (50000009071675367421/50000000000000000000 : ℝ)) (by norm_num) 4455 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25070117912907726719/25000000000000000000 : ℝ) ≤ (10006439804680561/10000000000000000 : ℝ) ^ (4455/1024 : ℝ) := by
    have hpowers : (25070117912907726719/25000000000000000000 : ℝ)^1024 ≤ (10006439804680561/10000000000000000 : ℝ)^4455 := by
      have hnat : (25070117912907726719 : ℕ)^1024*10000000000000000^4455 ≤ 10006439804680561^4455*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25070117912907726719 25000000000000000000 10006439804680561 10000000000000000 1024 4455 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10006439804680561/10000000000000000 : ℝ)) (X := (25070117912907726719/25000000000000000000 : ℝ)) (by norm_num) 4455 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10056092515991107891/10000000000000000000 : ℝ) ≤ (5006439596164401/5000000000000000 : ℝ) ^ (4455/1024 : ℝ) := by
    have hpowers : (10056092515991107891/10000000000000000000 : ℝ)^1024 ≤ (5006439596164401/5000000000000000 : ℝ)^4455 := by
      have hnat : (10056092515991107891 : ℕ)^1024*5000000000000000^4455 ≤ 5006439596164401^4455*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10056092515991107891 10000000000000000000 5006439596164401 5000000000000000 1024 4455 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5006439596164401/5000000000000000 : ℝ)) (X := (10056092515991107891/10000000000000000000 : ℝ)) (by norm_num) 4455 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(9071675367421/100000000000000000000 : ℝ) ≤ ((19579918622206595999/19582500000000000000 : ℝ)+2*(6439387648241/2349900000000000 : ℝ)*(1203/50000 : ℝ))^(4455/1024 : ℝ) := by
    rw [show (19579918622206595999/19582500000000000000 : ℝ)+2*(6439387648241/2349900000000000 : ℝ)*(1203/50000 : ℝ)=(15625000651613/15625000000000 : ℝ) by norm_num, show 1+2*(9071675367421/100000000000000000000 : ℝ)=(50000009071675367421/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(56092515991107891/20000000000000000000 : ℝ)+(9071675367421/100000000000000000000 : ℝ) ≤ ((19579918622206595999/19582500000000000000 : ℝ)+(6439387648241/2349900000000000 : ℝ)*((5181/20000 : ℝ)+(1203/50000 : ℝ)))^(4455/1024 : ℝ) := by
    rw [show (19579918622206595999/19582500000000000000 : ℝ)+(6439387648241/2349900000000000 : ℝ)*((5181/20000 : ℝ)+(1203/50000 : ℝ))=(10006439804680561/10000000000000000 : ℝ) by norm_num, show 1+(56092515991107891/20000000000000000000 : ℝ)+(9071675367421/100000000000000000000 : ℝ)=(25070117912907726719/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(56092515991107891/20000000000000000000 : ℝ) ≤ ((19579918622206595999/19582500000000000000 : ℝ)+2*(6439387648241/2349900000000000 : ℝ)*(5181/20000 : ℝ))^(4455/1024 : ℝ) := by
    rw [show (19579918622206595999/19582500000000000000 : ℝ)+2*(6439387648241/2349900000000000 : ℝ)*(5181/20000 : ℝ)=(5006439596164401/5000000000000000 : ℝ) by norm_num, show 1+2*(56092515991107891/20000000000000000000 : ℝ)=(10056092515991107891/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (19579918622206595999/19582500000000000000 : ℝ)*(X 1 0+X 2 0)+(6439387648241/2349900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4455/1024 : ℝ)) (lo := (1203/50000 : ℝ)) (hi := (5181/20000 : ℝ)) (c := (19579918622206595999/19582500000000000000 : ℝ)) (alpha := (6439387648241/2349900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (19579918622206595999/19582500000000000000 : ℝ)*(X 0 1+X 2 1)+(6439387648241/2349900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4455/1024 : ℝ)) (lo := (1203/50000 : ℝ)) (hi := (5181/20000 : ℝ)) (c := (19579918622206595999/19582500000000000000 : ℝ)) (alpha := (6439387648241/2349900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (19579918622206595999/19582500000000000000 : ℝ)*(X 0 2+X 1 2)+(6439387648241/2349900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4455/1024 : ℝ)) (lo := (1203/50000 : ℝ)) (hi := (5181/20000 : ℝ)) (c := (19579918622206595999/19582500000000000000 : ℝ)) (alpha := (6439387648241/2349900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-235338993/1250000000 : ℝ)*X 0 0+(5592737793/10000000000 : ℝ)*X 0 1+(1016461571/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1480_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2696281897/5000000000 : ℝ)*X 1 0+(-1076305797/5000000000 : ℝ)*X 1 1+(2541154109/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1480_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5392564251/10000000000 : ℝ)*X 2 0+(158822123/312500000 : ℝ)*X 2 1+(-2152611357/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1480_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4261265627/10000000000 : ℝ)*X 0 0+(3728118739/10000000000 : ℝ)*X 0 1+(4859511567/10000000000 : ℝ)*X 0 2+(4261265627/10000000000 : ℝ)*X 1 0+(3728118739/10000000000 : ℝ)*X 1 1+(4859511567/10000000000 : ℝ)*X 1 2+(4261265627/10000000000 : ℝ)*X 2 0+(3728118739/10000000000 : ℝ)*X 2 1+(4859511567/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1480_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-235385157/1250000000 : ℝ)*X 0 0+(254414019/500000000 : ℝ)*X 0 1+(139666611/250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1480_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1314665629/2500000000 : ℝ)*X 1 0+(-51507969/312500000 : ℝ)*X 1 1+(34916653/62500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1480_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5258662539/10000000000 : ℝ)*X 2 0+(111733289/200000000 : ℝ)*X 2 1+(-1648255019/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1480_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((852416871/2000000000 : ℝ)*X 0 0+(4846273681/10000000000 : ℝ)*X 0 1+(7483161/20000000 : ℝ)*X 0 2+(852416871/2000000000 : ℝ)*X 1 0+(4846273681/10000000000 : ℝ)*X 1 1+(7483161/20000000 : ℝ)*X 1 2+(852416871/2000000000 : ℝ)*X 2 0+(4846273681/10000000000 : ℝ)*X 2 1+(7483161/20000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1480_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (98622934083883050678120881/34968750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (108615417/20000000000000 : ℝ)*(base19) + (352425921/50000000000000 : ℝ)*(base23) + (3303301/20000000000000 : ℝ)*(upper3) + (1147367/50000000000000 : ℝ)*(upper4) + (159789291/100000000000000 : ℝ)*(upper5) + (355376745109361/25000000000000 : ℝ)*(major0) + (355376745109361/25000000000000 : ℝ)*(major1) + (355376745109361/25000000000000 : ℝ)*(major2) + (979568315358457/50000000000000 : ℝ)*(sp0) + (195914246544807/10000000000000 : ℝ)*(sp1) + (61223196989791/3125000000000 : ℝ)*(sp2) + (883868832553853/100000000000000 : ℝ)*(sp3) + (6377808241/100000000000000 : ℝ)*(sp4) + (1012892667/50000000000000 : ℝ)*(sp7) + (883870858339187/100000000000000 : ℝ)*(f.failure) + (391828601705031/20000000000000 : ℝ)*(f.sum) + (109796208222949/117495000000000000000000000000 : ℝ)*base65 + (7721928967893397583/1468687500000000000000000000000000 : ℝ)*base68 + (5887282667083522583/1468687500000000000000000000000000 : ℝ)*base70 + (1415604819969772583/1468687500000000000000000000000000 : ℝ)*base72 + (294846391070291/117495000000000000000000000000 : ℝ)*base74 + (316409639463352417/1468687500000000000000000000000000 : ℝ)*base75 + (13264232623138477417/1468687500000000000000000000000000 : ℝ)*base77 + (1603761124977772583/1468687500000000000000000000000000 : ℝ)*base80 + (673917927735161/117495000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (759619/2500000000000000000000 : ℝ)*base90 + (759619/2500000000000000000000 : ℝ)*base92 + (759619/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (967101925619270741252935517/244781250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (763295463/100000000000000 : ℝ)*(base19) + (163181507/20000000000000 : ℝ)*(base23) + (22198969/20000000000000 : ℝ)*(upper3) + (16147031/100000000000000 : ℝ)*(lower4) + (36104049/50000000000000 : ℝ)*(upper5) + (727928286856661/50000000000000 : ℝ)*(major0) + (727928286856661/50000000000000 : ℝ)*(major1) + (727928286856661/50000000000000 : ℝ)*(major2) + (1159393703/25000000000000 : ℝ)*(sp1) + (5153234369/100000000000000 : ℝ)*(sp2) + (3135131431727/156250000000 : ℝ)*(sp4) + (1003239357717503/50000000000000 : ℝ)*(sp5) + (125404884197711/6250000000000 : ℝ)*(sp6) + (905228899425281/100000000000000 : ℝ)*(sp7) + (905228899425281/100000000000000 : ℝ)*(f.failure) + (3135131431727/156250000000 : ℝ)*(f.sum) + (369653328989477/117495000000000000000000000000 : ℝ)*base65 + (13439112583462448017/2937375000000000000000000000000000 : ℝ)*base67 + (12022723458857676983/2937375000000000000000000000000000 : ℝ)*base70 + (681832527560301983/2937375000000000000000000000000000 : ℝ)*base72 + (423113329574027/117495000000000000000000000000 : ℝ)*base73 + (19148644509770676983/2937375000000000000000000000000000 : ℝ)*base76 + (487738010565426983/2937375000000000000000000000000000 : ℝ)*base78 + (5252665215889551983/2937375000000000000000000000000000 : ℝ)*base80 + (523280536597783/117495000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1903503/2500000000000000000000 : ℝ)*base89 + (1903503/2500000000000000000000 : ℝ)*base91 + (1903503/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1480_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4455/1024 : ℝ) ≤ p) (hpb : p ≤ (4457/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (40206863/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (5181/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1203/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (3953/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2337/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1480_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1480_s2_0 (p : ℝ) (hpa : (4455/1024 : ℝ) ≤ p) (hpb : p ≤ (4457/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-955578223/5000000000 : ℝ)*x 0 + (683614291/1250000000 : ℝ)*x 1 + (2593884771/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (955578223/5000000000 : ℝ)^4457 ≤ (11665954692023/100000000000000 : ℝ)^3433 := by
    have hnat : (955578223 : ℕ)^4457*100000000000000^3433 ≤ 11665954692023^3433*5000000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      955578223 5000000000 11665954692023 100000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (683614291/1250000000 : ℝ)^4457 ≤ (22839779515237/50000000000000 : ℝ)^3433 := by
    have hnat : (683614291 : ℕ)^4457*50000000000000^3433 ≤ 22839779515237^3433*1250000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      683614291 1250000000 22839779515237 50000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2593884771/5000000000 : ℝ)^4457 ≤ (1706179450421/4000000000000 : ℝ)^3433 := by
    have hnat : (2593884771 : ℕ)^4457*4000000000000^3433 ≤ 1706179450421^3433*5000000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2593884771 5000000000 1706179450421 4000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4457/1024 : ℝ)) 4457 3433 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-955578223/5000000000 : ℝ), (683614291/1250000000 : ℝ), (2593884771/5000000000 : ℝ)] ![(11665954692023/100000000000000 : ℝ), (22839779515237/50000000000000 : ℝ), (1706179450421/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-955578223/5000000000 : ℝ)|^4457 ≤ (11665954692023/100000000000000 : ℝ)^3433
        have hw : |(-955578223/5000000000 : ℝ)|=(955578223/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(683614291/1250000000 : ℝ)|^4457 ≤ (22839779515237/50000000000000 : ℝ)^3433
        have hw : |(683614291/1250000000 : ℝ)|=(683614291/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2593884771/5000000000 : ℝ)|^4457 ≤ (1706179450421/4000000000000 : ℝ)^3433
        have hw : |(2593884771/5000000000 : ℝ)|=(2593884771/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1480_s2_1 (p : ℝ) (hpa : (4455/1024 : ℝ) ≤ p) (hpb : p ≤ (4457/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (268071547/500000000 : ℝ)*x 0 + (-2056184433/10000000000 : ℝ)*x 1 + (2593884967/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (268071547/500000000 : ℝ)^4457 ≤ (44517441118087/100000000000000 : ℝ)^3433 := by
    have hnat : (268071547 : ℕ)^4457*100000000000000^3433 ≤ 44517441118087^3433*500000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      268071547 500000000 44517441118087 100000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2056184433/10000000000 : ℝ)^4457 ≤ (3207017105539/25000000000000 : ℝ)^3433 := by
    have hnat : (2056184433 : ℕ)^4457*25000000000000^3433 ≤ 3207017105539^3433*10000000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2056184433 10000000000 3207017105539 25000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2593884967/5000000000 : ℝ)^4457 ≤ (42654490444981/100000000000000 : ℝ)^3433 := by
    have hnat : (2593884967 : ℕ)^4457*100000000000000^3433 ≤ 42654490444981^3433*5000000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2593884967 5000000000 42654490444981 100000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4457/1024 : ℝ)) 4457 3433 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(268071547/500000000 : ℝ), (-2056184433/10000000000 : ℝ), (2593884967/5000000000 : ℝ)] ![(44517441118087/100000000000000 : ℝ), (3207017105539/25000000000000 : ℝ), (42654490444981/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(268071547/500000000 : ℝ)|^4457 ≤ (44517441118087/100000000000000 : ℝ)^3433
        have hw : |(268071547/500000000 : ℝ)|=(268071547/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2056184433/10000000000 : ℝ)|^4457 ≤ (3207017105539/25000000000000 : ℝ)^3433
        have hw : |(-2056184433/10000000000 : ℝ)|=(2056184433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2593884967/5000000000 : ℝ)|^4457 ≤ (42654490444981/100000000000000 : ℝ)^3433
        have hw : |(2593884967/5000000000 : ℝ)|=(2593884967/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1480_s2_2 (p : ℝ) (hpa : (4455/1024 : ℝ) ≤ p) (hpb : p ≤ (4457/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5361431183/10000000000 : ℝ)*x 0 + (2593884971/5000000000 : ℝ)*x 1 + (-2056184099/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5361431183/10000000000 : ℝ)^4457 ≤ (5564680467203/12500000000000 : ℝ)^3433 := by
    have hnat : (5361431183 : ℕ)^4457*12500000000000^3433 ≤ 5564680467203^3433*10000000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5361431183 10000000000 5564680467203 12500000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2593884971/5000000000 : ℝ)^4457 ≤ (21327245265189/50000000000000 : ℝ)^3433 := by
    have hnat : (2593884971 : ℕ)^4457*50000000000000^3433 ≤ 21327245265189^3433*5000000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2593884971 5000000000 21327245265189 50000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2056184099/10000000000 : ℝ)^4457 ≤ (12828065716861/100000000000000 : ℝ)^3433 := by
    have hnat : (2056184099 : ℕ)^4457*100000000000000^3433 ≤ 12828065716861^3433*10000000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2056184099 10000000000 12828065716861 100000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4457/1024 : ℝ)) 4457 3433 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5361431183/10000000000 : ℝ), (2593884971/5000000000 : ℝ), (-2056184099/10000000000 : ℝ)] ![(5564680467203/12500000000000 : ℝ), (21327245265189/50000000000000 : ℝ), (12828065716861/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5361431183/10000000000 : ℝ)|^4457 ≤ (5564680467203/12500000000000 : ℝ)^3433
        have hw : |(5361431183/10000000000 : ℝ)|=(5361431183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2593884971/5000000000 : ℝ)|^4457 ≤ (21327245265189/50000000000000 : ℝ)^3433
        have hw : |(2593884971/5000000000 : ℝ)|=(2593884971/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2056184099/10000000000 : ℝ)|^4457 ≤ (12828065716861/100000000000000 : ℝ)^3433
        have hw : |(-2056184099/10000000000 : ℝ)|=(2056184099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1480_s2_3 (p : ℝ) (hpa : (4455/1024 : ℝ) ≤ p) (hpb : p ≤ (4457/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (428156511/1000000000 : ℝ)*x 0 + (3979854699/10000000000 : ℝ)*x 1 + (4603026047/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (428156511/1000000000 : ℝ)^4457 ≤ (33244243248201/100000000000000 : ℝ)^3433 := by
    have hnat : (428156511 : ℕ)^4457*100000000000000^3433 ≤ 33244243248201^3433*1000000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      428156511 1000000000 33244243248201 100000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3979854699/10000000000 : ℝ)^4457 ≤ (6047070764903/20000000000000 : ℝ)^3433 := by
    have hnat : (3979854699 : ℕ)^4457*20000000000000^3433 ≤ 6047070764903^3433*10000000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3979854699 10000000000 6047070764903 20000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4603026047/10000000000 : ℝ)^4457 ≤ (1826020145599/5000000000000 : ℝ)^3433 := by
    have hnat : (4603026047 : ℕ)^4457*5000000000000^3433 ≤ 1826020145599^3433*10000000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4603026047 10000000000 1826020145599 5000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4457/1024 : ℝ)) 4457 3433 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(428156511/1000000000 : ℝ), (3979854699/10000000000 : ℝ), (4603026047/10000000000 : ℝ)] ![(33244243248201/100000000000000 : ℝ), (6047070764903/20000000000000 : ℝ), (1826020145599/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(428156511/1000000000 : ℝ)|^4457 ≤ (33244243248201/100000000000000 : ℝ)^3433
        have hw : |(428156511/1000000000 : ℝ)|=(428156511/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3979854699/10000000000 : ℝ)|^4457 ≤ (6047070764903/20000000000000 : ℝ)^3433
        have hw : |(3979854699/10000000000 : ℝ)|=(3979854699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4603026047/10000000000 : ℝ)|^4457 ≤ (1826020145599/5000000000000 : ℝ)^3433
        have hw : |(4603026047/10000000000 : ℝ)|=(4603026047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1480_s2_4 (p : ℝ) (hpa : (4455/1024 : ℝ) ≤ p) (hpb : p ≤ (4457/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-955609263/5000000000 : ℝ)*x 0 + (5189590737/10000000000 : ℝ)*x 1 + (683384503/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (955609263/5000000000 : ℝ)^4457 ≤ (11666446671163/100000000000000 : ℝ)^3433 := by
    have hnat : (955609263 : ℕ)^4457*100000000000000^3433 ≤ 11666446671163^3433*5000000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      955609263 5000000000 11666446671163 100000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5189590737/10000000000 : ℝ)^4457 ≤ (21336963931443/50000000000000 : ℝ)^3433 := by
    have hnat : (5189590737 : ℕ)^4457*50000000000000^3433 ≤ 21336963931443^3433*10000000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5189590737 10000000000 21336963931443 50000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (683384503/1250000000 : ℝ)^4457 ≤ (45659625456537/100000000000000 : ℝ)^3433 := by
    have hnat : (683384503 : ℕ)^4457*100000000000000^3433 ≤ 45659625456537^3433*1250000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      683384503 1250000000 45659625456537 100000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4457/1024 : ℝ)) 4457 3433 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-955609263/5000000000 : ℝ), (5189590737/10000000000 : ℝ), (683384503/1250000000 : ℝ)] ![(11666446671163/100000000000000 : ℝ), (21336963931443/50000000000000 : ℝ), (45659625456537/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-955609263/5000000000 : ℝ)|^4457 ≤ (11666446671163/100000000000000 : ℝ)^3433
        have hw : |(-955609263/5000000000 : ℝ)|=(955609263/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5189590737/10000000000 : ℝ)|^4457 ≤ (21336963931443/50000000000000 : ℝ)^3433
        have hw : |(5189590737/10000000000 : ℝ)|=(5189590737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(683384503/1250000000 : ℝ)|^4457 ≤ (45659625456537/100000000000000 : ℝ)^3433
        have hw : |(683384503/1250000000 : ℝ)|=(683384503/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1480_s2_5 (p : ℝ) (hpa : (4455/1024 : ℝ) ≤ p) (hpb : p ≤ (4457/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (528797583/1000000000 : ℝ)*x 0 + (-888439119/5000000000 : ℝ)*x 1 + (5467076043/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (528797583/1000000000 : ℝ)^4457 ≤ (5465902383999/12500000000000 : ℝ)^3433 := by
    have hnat : (528797583 : ℕ)^4457*12500000000000^3433 ≤ 5465902383999^3433*1000000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528797583 1000000000 5465902383999 12500000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (888439119/5000000000 : ℝ)^4457 ≤ (1061315525599/10000000000000 : ℝ)^3433 := by
    have hnat : (888439119 : ℕ)^4457*10000000000000^3433 ≤ 1061315525599^3433*5000000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      888439119 5000000000 1061315525599 10000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5467076043/10000000000 : ℝ)^4457 ≤ (5707453207819/12500000000000 : ℝ)^3433 := by
    have hnat : (5467076043 : ℕ)^4457*12500000000000^3433 ≤ 5707453207819^3433*10000000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5467076043 10000000000 5707453207819 12500000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4457/1024 : ℝ)) 4457 3433 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(528797583/1000000000 : ℝ), (-888439119/5000000000 : ℝ), (5467076043/10000000000 : ℝ)] ![(5465902383999/12500000000000 : ℝ), (1061315525599/10000000000000 : ℝ), (5707453207819/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(528797583/1000000000 : ℝ)|^4457 ≤ (5465902383999/12500000000000 : ℝ)^3433
        have hw : |(528797583/1000000000 : ℝ)|=(528797583/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-888439119/5000000000 : ℝ)|^4457 ≤ (1061315525599/10000000000000 : ℝ)^3433
        have hw : |(-888439119/5000000000 : ℝ)|=(888439119/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5467076043/10000000000 : ℝ)|^4457 ≤ (5707453207819/12500000000000 : ℝ)^3433
        have hw : |(5467076043/10000000000 : ℝ)|=(5467076043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1480_s2_6 (p : ℝ) (hpa : (4455/1024 : ℝ) ≤ p) (hpb : p ≤ (4457/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5287976137/10000000000 : ℝ)*x 0 + (5467076087/10000000000 : ℝ)*x 1 + (-1776877751/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5287976137/10000000000 : ℝ)^4457 ≤ (43727222367859/100000000000000 : ℝ)^3433 := by
    have hnat : (5287976137 : ℕ)^4457*100000000000000^3433 ≤ 43727222367859^3433*10000000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5287976137 10000000000 43727222367859 100000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5467076087/10000000000 : ℝ)^4457 ≤ (1141490653491/2500000000000 : ℝ)^3433 := by
    have hnat : (5467076087 : ℕ)^4457*2500000000000^3433 ≤ 1141490653491^3433*10000000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5467076087 10000000000 1141490653491 2500000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1776877751/10000000000 : ℝ)^4457 ≤ (10613151479533/100000000000000 : ℝ)^3433 := by
    have hnat : (1776877751 : ℕ)^4457*100000000000000^3433 ≤ 10613151479533^3433*10000000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1776877751 10000000000 10613151479533 100000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4457/1024 : ℝ)) 4457 3433 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5287976137/10000000000 : ℝ), (5467076087/10000000000 : ℝ), (-1776877751/10000000000 : ℝ)] ![(43727222367859/100000000000000 : ℝ), (1141490653491/2500000000000 : ℝ), (10613151479533/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5287976137/10000000000 : ℝ)|^4457 ≤ (43727222367859/100000000000000 : ℝ)^3433
        have hw : |(5287976137/10000000000 : ℝ)|=(5287976137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5467076087/10000000000 : ℝ)|^4457 ≤ (1141490653491/2500000000000 : ℝ)^3433
        have hw : |(5467076087/10000000000 : ℝ)|=(5467076087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1776877751/10000000000 : ℝ)|^4457 ≤ (10613151479533/100000000000000 : ℝ)^3433
        have hw : |(-1776877751/10000000000 : ℝ)|=(1776877751/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1480_s2_7 (p : ℝ) (hpa : (4455/1024 : ℝ) ≤ p) (hpb : p ≤ (4457/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2140851111/5000000000 : ℝ)*x 0 + (287436799/625000000 : ℝ)*x 1 + (3983929689/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2140851111/5000000000 : ℝ)^4457 ≤ (8311406353601/25000000000000 : ℝ)^3433 := by
    have hnat : (2140851111 : ℕ)^4457*25000000000000^3433 ≤ 8311406353601^3433*5000000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2140851111 5000000000 8311406353601 25000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (287436799/625000000 : ℝ)^4457 ≤ (911970556787/2500000000000 : ℝ)^3433 := by
    have hnat : (287436799 : ℕ)^4457*2500000000000^3433 ≤ 911970556787^3433*625000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      287436799 625000000 911970556787 2500000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3983929689/10000000000 : ℝ)^4457 ≤ (6055110458741/20000000000000 : ℝ)^3433 := by
    have hnat : (3983929689 : ℕ)^4457*20000000000000^3433 ≤ 6055110458741^3433*10000000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3983929689 10000000000 6055110458741 20000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4457/1024 : ℝ)) 4457 3433 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2140851111/5000000000 : ℝ), (287436799/625000000 : ℝ), (3983929689/10000000000 : ℝ)] ![(8311406353601/25000000000000 : ℝ), (911970556787/2500000000000 : ℝ), (6055110458741/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2140851111/5000000000 : ℝ)|^4457 ≤ (8311406353601/25000000000000 : ℝ)^3433
        have hw : |(2140851111/5000000000 : ℝ)|=(2140851111/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(287436799/625000000 : ℝ)|^4457 ≤ (911970556787/2500000000000 : ℝ)^3433
        have hw : |(287436799/625000000 : ℝ)|=(287436799/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3983929689/10000000000 : ℝ)|^4457 ≤ (6055110458741/20000000000000 : ℝ)^3433
        have hw : |(3983929689/10000000000 : ℝ)|=(3983929689/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1480_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4455/1024 : ℝ) ≤ p) (hpb : p ≤ (4457/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (40206863/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2337/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3953/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (1273/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16131/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2337/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (3953/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2337/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (3953/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2337/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (3953/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2337/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (3953/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2337/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (3953/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2337/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (3953/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (3953/50000 : ℝ) ^ (4455/1024 : ℝ) ≤ (802484031920209/50000000000000000000 : ℝ) := by
    have hpowers : (3953/50000 : ℝ)^4455 ≤ (802484031920209/50000000000000000000 : ℝ)^1024 := by
      have hnat : (3953 : ℕ)^4455*50000000000000000000^1024 ≤ 802484031920209^1024*50000^4455 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3953 50000 802484031920209 50000000000000000000 4455 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3953/50000 : ℝ)) (X := (802484031920209/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4455 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2337/12500 : ℝ) ^ (4455/1024 : ℝ) ≤ (67870356839962327/100000000000000000000 : ℝ) := by
    have hpowers : (2337/12500 : ℝ)^4455 ≤ (67870356839962327/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2337 : ℕ)^4455*100000000000000000000^1024 ≤ 67870356839962327^1024*12500^4455 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2337 12500 67870356839962327 100000000000000000000 4455 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2337/12500 : ℝ)) (X := (67870356839962327/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4455 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000802484031920209/25000000000000000000 : ℝ) ≤ (2500018445196221/2500000000000000 : ℝ) ^ (4455/1024 : ℝ) := by
    have hpowers : (25000802484031920209/25000000000000000000 : ℝ)^1024 ≤ (2500018445196221/2500000000000000 : ℝ)^4455 := by
      have hnat : (25000802484031920209 : ℕ)^1024*2500000000000000^4455 ≤ 2500018445196221^4455*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000802484031920209 25000000000000000000 2500018445196221 2500000000000000 1024 4455 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500018445196221/2500000000000000 : ℝ)) (X := (25000802484031920209/25000000000000000000 : ℝ)) (by norm_num) 4455 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20013895064980760549/20000000000000000000 : ℝ) ≤ (10001596491753897/10000000000000000 : ℝ) ^ (4455/1024 : ℝ) := by
    have hpowers : (20013895064980760549/20000000000000000000 : ℝ)^1024 ≤ (10001596491753897/10000000000000000 : ℝ)^4455 := by
      have hnat : (20013895064980760549 : ℕ)^1024*10000000000000000^4455 ≤ 10001596491753897^4455*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20013895064980760549 20000000000000000000 10001596491753897 10000000000000000 1024 4455 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001596491753897/10000000000000000 : ℝ)) (X := (20013895064980760549/20000000000000000000 : ℝ)) (by norm_num) 4455 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50067870356839962327/50000000000000000000 : ℝ) ≤ (1000311920272291/1000000000000000 : ℝ) ^ (4455/1024 : ℝ) := by
    have hpowers : (50067870356839962327/50000000000000000000 : ℝ)^1024 ≤ (1000311920272291/1000000000000000 : ℝ)^4455 := by
      have hnat : (50067870356839962327 : ℕ)^1024*1000000000000000^4455 ≤ 1000311920272291^4455*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50067870356839962327 50000000000000000000 1000311920272291 1000000000000000 1024 4455 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000311920272291/1000000000000000 : ℝ)) (X := (50067870356839962327/50000000000000000000 : ℝ)) (by norm_num) 4455 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(802484031920209/50000000000000000000 : ℝ) ≤ ((2074552288246670477/2075000000000000000 : ℝ)+2*(117131613001/83000000000000 : ℝ)*(3953/50000 : ℝ))^(4455/1024 : ℝ) := by
    rw [show (2074552288246670477/2075000000000000000 : ℝ)+2*(117131613001/83000000000000 : ℝ)*(3953/50000 : ℝ)=(2500018445196221/2500000000000000 : ℝ) by norm_num, show 1+2*(802484031920209/50000000000000000000 : ℝ)=(25000802484031920209/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(67870356839962327/100000000000000000000 : ℝ)+(802484031920209/50000000000000000000 : ℝ) ≤ ((2074552288246670477/2075000000000000000 : ℝ)+(117131613001/83000000000000 : ℝ)*((2337/12500 : ℝ)+(3953/50000 : ℝ)))^(4455/1024 : ℝ) := by
    rw [show (2074552288246670477/2075000000000000000 : ℝ)+(117131613001/83000000000000 : ℝ)*((2337/12500 : ℝ)+(3953/50000 : ℝ))=(10001596491753897/10000000000000000 : ℝ) by norm_num, show 1+(67870356839962327/100000000000000000000 : ℝ)+(802484031920209/50000000000000000000 : ℝ)=(20013895064980760549/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(67870356839962327/100000000000000000000 : ℝ) ≤ ((2074552288246670477/2075000000000000000 : ℝ)+2*(117131613001/83000000000000 : ℝ)*(2337/12500 : ℝ))^(4455/1024 : ℝ) := by
    rw [show (2074552288246670477/2075000000000000000 : ℝ)+2*(117131613001/83000000000000 : ℝ)*(2337/12500 : ℝ)=(1000311920272291/1000000000000000 : ℝ) by norm_num, show 1+2*(67870356839962327/100000000000000000000 : ℝ)=(50067870356839962327/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2074552288246670477/2075000000000000000 : ℝ)*(X 1 0+X 2 0)+(117131613001/83000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4455/1024 : ℝ)) (lo := (3953/50000 : ℝ)) (hi := (2337/12500 : ℝ)) (c := (2074552288246670477/2075000000000000000 : ℝ)) (alpha := (117131613001/83000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2074552288246670477/2075000000000000000 : ℝ)*(X 0 1+X 2 1)+(117131613001/83000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4455/1024 : ℝ)) (lo := (3953/50000 : ℝ)) (hi := (2337/12500 : ℝ)) (c := (2074552288246670477/2075000000000000000 : ℝ)) (alpha := (117131613001/83000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2074552288246670477/2075000000000000000 : ℝ)*(X 0 2+X 1 2)+(117131613001/83000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4455/1024 : ℝ)) (lo := (3953/50000 : ℝ)) (hi := (2337/12500 : ℝ)) (c := (2074552288246670477/2075000000000000000 : ℝ)) (alpha := (117131613001/83000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-955578223/5000000000 : ℝ)*X 0 0+(683614291/1250000000 : ℝ)*X 0 1+(2593884771/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1480_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((268071547/500000000 : ℝ)*X 1 0+(-2056184433/10000000000 : ℝ)*X 1 1+(2593884967/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1480_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5361431183/10000000000 : ℝ)*X 2 0+(2593884971/5000000000 : ℝ)*X 2 1+(-2056184099/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1480_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((428156511/1000000000 : ℝ)*X 0 0+(3979854699/10000000000 : ℝ)*X 0 1+(4603026047/10000000000 : ℝ)*X 0 2+(428156511/1000000000 : ℝ)*X 1 0+(3979854699/10000000000 : ℝ)*X 1 1+(4603026047/10000000000 : ℝ)*X 1 2+(428156511/1000000000 : ℝ)*X 2 0+(3979854699/10000000000 : ℝ)*X 2 1+(4603026047/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1480_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-955609263/5000000000 : ℝ)*X 0 0+(5189590737/10000000000 : ℝ)*X 0 1+(683384503/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1480_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((528797583/1000000000 : ℝ)*X 1 0+(-888439119/5000000000 : ℝ)*X 1 1+(5467076043/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1480_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5287976137/10000000000 : ℝ)*X 2 0+(5467076087/10000000000 : ℝ)*X 2 1+(-1776877751/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1480_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2140851111/5000000000 : ℝ)*X 0 0+(287436799/625000000 : ℝ)*X 0 1+(3983929689/10000000000 : ℝ)*X 0 2+(2140851111/5000000000 : ℝ)*X 1 0+(287436799/625000000 : ℝ)*X 1 1+(3983929689/10000000000 : ℝ)*X 1 2+(2140851111/5000000000 : ℝ)*X 2 0+(287436799/625000000 : ℝ)*X 2 1+(3983929689/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1480_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (106157981835953893405598649/10375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (298263343/25000000000000 : ℝ)*(base19) + (1111736821/100000000000000 : ℝ)*(base23) + (130030477/100000000000000 : ℝ)*(lower2) + (9387577/6250000000000 : ℝ)*(upper3) + (243770199/100000000000000 : ℝ)*(upper5) + (258081678472321/10000000000000 : ℝ)*(major0) + (258081678472321/10000000000000 : ℝ)*(major1) + (258081678472321/10000000000000 : ℝ)*(major2) + (44461268182069/1250000000000 : ℝ)*(sp0) + (3556920431284867/100000000000000 : ℝ)*(sp1) + (1778460256300709/50000000000000 : ℝ)*(sp2) + (200587902783847/12500000000000 : ℝ)*(sp3) + (10084886359/50000000000000 : ℝ)*(sp4) + (335270703/4000000000000 : ℝ)*(sp7) + (100294475252397/6250000000000 : ℝ)*(f.failure) + (3556921624338239/100000000000000 : ℝ)*(f.sum) + (2121913255191/415000000000000000000000000 : ℝ)*base65 + (185380648972892117/20750000000000000000000000000000 : ℝ)*base67 + (234406616516142117/20750000000000000000000000000000 : ℝ)*base69 + (81736654107107883/20750000000000000000000000000000 : ℝ)*base72 + (855735311463/207500000000000000000000000 : ℝ)*base73 + (59996979616642117/20750000000000000000000000000000 : ℝ)*base75 + (187439971227392117/20750000000000000000000000000000 : ℝ)*base77 + (31583302149607883/20750000000000000000000000000000 : ℝ)*base80 + (1100895637673/207500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (975611/156250000000000000000 : ℝ)*base89 + (975611/156250000000000000000 : ℝ)*base91 + (975611/156250000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (870555594499868675861609769/103750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (928815399/100000000000000 : ℝ)*(base19) + (1300144931/100000000000000 : ℝ)*(base23) + (68919561/50000000000000 : ℝ)*(upper3) + (39278891/100000000000000 : ℝ)*(lower4) + (8926359/4000000000000 : ℝ)*(upper5) + (2614828728685199/100000000000000 : ℝ)*(major0) + (2614828728685199/100000000000000 : ℝ)*(major1) + (2614828728685199/100000000000000 : ℝ)*(major2) + (5192028401/50000000000000 : ℝ)*(sp1) + (1044166939/6250000000000 : ℝ)*(sp2) + (900949369405963/25000000000000 : ℝ)*(sp4) + (900946541187913/25000000000000 : ℝ)*(sp5) + (3603779470807897/100000000000000 : ℝ)*(sp6) + (406464925012491/25000000000000 : ℝ)*(sp7) + (406464925012491/25000000000000 : ℝ)*(f.failure) + (900949369405963/25000000000000 : ℝ)*(f.sum) + (15010117430201/4150000000000000000000000000 : ℝ)*base66 + (177592499824855077/207500000000000000000000000000000 : ℝ)*base68 + (1400768089295144923/207500000000000000000000000000000 : ℝ)*base69 + (1373784837034855077/207500000000000000000000000000000 : ℝ)*base72 + (14736854363901/4150000000000000000000000000 : ℝ)*base74 + (736054389324855077/207500000000000000000000000000000 : ℝ)*base76 + (326837412042355077/207500000000000000000000000000000 : ℝ)*base78 + (1826948650152644923/207500000000000000000000000000000 : ℝ)*base79 + (3881527854249/4150000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (5175733/625000000000000000000 : ℝ)*base89 + (5175733/625000000000000000000 : ℝ)*base91 + (5175733/625000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1480_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4455/1024 : ℝ) ≤ p) (hpb : p ≤ (4457/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (40206863/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2337/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3953/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1273/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16131/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1480_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1480_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4455/1024 : ℝ) ≤ p) (hpb : p ≤ (4457/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (40206863/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1273/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16131/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1480_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1480_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1480_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4455/1024 : ℝ) ≤ p) (hpb : p ≤ (4457/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (40206863/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1273/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16131/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1480_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
