-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff12.convex_retained_localization
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-27T00:31:42.357497+00:00
-- url     : https://prove2.me/submissions/7f81e089-65be-43a0-84dc-13c0bfbc6cad

import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.Convex.Function
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Basic
import Definitions.Def_HlawkaSchatten_GapComparison
import Mathlib.Analysis.Convex.Function
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction
open scoped BigOperators
namespace HlawkaSchatten.DiagonalConstruction
variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E]
theorem lpNorm_eq_piLp {p : ℝ} (hp : 0 < p) (x : ι → E) :
    lpNorm p x = ‖WithLp.toLp (ENNReal.ofReal p) x‖ := by
  rw [PiLp.norm_eq_sum (by simpa only [ENNReal.toReal_ofReal hp.le] using hp)]
  simp [lpNorm, ENNReal.toReal_ofReal hp.le]
theorem lpNorm_add {p : ℝ} (hp : 1 ≤ p) (x y : ι → E) :
    lpNorm p (x + y) ≤ lpNorm p x + lpNorm p y := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  let : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp⟩
  simpa only [lpNorm_eq_piLp hp0, ← WithLp.toLp_add] using
    norm_add_le (WithLp.toLp (ENNReal.ofReal p) x) (WithLp.toLp (ENNReal.ofReal p) y)
theorem norm_apply_le_lpNorm {p : ℝ} (hp : 1 ≤ p) (x : ι → E) (i : ι) :
    ‖x i‖ ≤ lpNorm p x := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  let : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp⟩
  rw [lpNorm_eq_piLp hp0]
  exact PiLp.norm_apply_le (WithLp.toLp (ENNReal.ofReal p) x) i
theorem lpNorm_smul [NormedSpace ℝ E] {p : ℝ} (hp : 0 < p)
    (c : ℝ) (x : ι → E) : lpNorm p (c • x) = |c| * lpNorm p x := by
  unfold lpNorm
  simp only [Pi.smul_apply, norm_smul, Real.norm_eq_abs,
    Real.mul_rpow (abs_nonneg c) (norm_nonneg _), ← Finset.mul_sum]
  rw [Real.mul_rpow (Real.rpow_nonneg (abs_nonneg c) _)
    (Finset.sum_nonneg fun i _ ↦ Real.rpow_nonneg (norm_nonneg (x i)) _),
    ← Real.rpow_mul (abs_nonneg c), mul_one_div_cancel hp.ne', Real.rpow_one]
theorem convexOn_lpNorm [NormedSpace ℝ E] {p : ℝ} (hp : 1 ≤ p) :
    ConvexOn ℝ Set.univ (lpNorm p : (ι → E) → ℝ) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb _
  have hp0 := zero_lt_one.trans_le hp
  simpa only [lpNorm_smul hp0, abs_of_nonneg ha, abs_of_nonneg hb, smul_eq_mul]
    using lpNorm_add hp (a • x) (b • y)
theorem pairGap_nonneg {p : ℝ} (hp : 1 ≤ p) (x y : ι → E) :
    0 ≤ pairGap (lpNorm p) x y := sub_nonneg.mpr (lpNorm_add hp x y)

end HlawkaSchatten.DiagonalConstruction

set_option autoImplicit false
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction
namespace HlawkaSchatten.DiagonalCutoff12

/- These inequalities, unlike equality of the norm sum, survive averaging. -/
theorem norm_sum_budget_convex {p : ℝ} (hp : 1 ≤ p) (R : ℝ) :
    Convex ℝ {X : Fin 3 → Fin 3 → ℝ | (∑ j, lpNorm p (X j)) ≤ R} := by
  intro X hX Y hY a b ha hb hab
  have hrow (j : Fin 3) : lpNorm p ((a • X+b • Y) j) ≤
      a*lpNorm p (X j)+b*lpNorm p (Y j) := by
    exact (convexOn_lpNorm (ι := Fin 3) (E := ℝ) hp).2
      (Set.mem_univ (X j)) (Set.mem_univ (Y j)) ha hb hab
  calc
    _ ≤ ∑ j, (a*lpNorm p (X j)+b*lpNorm p (Y j)) :=
      Finset.sum_le_sum fun j _ ↦ hrow j
    _ = a*(∑ j, lpNorm p (X j))+b*(∑ j, lpNorm p (Y j)) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ a*R+b*R := add_le_add (mul_le_mul_of_nonneg_left hX ha)
      (mul_le_mul_of_nonneg_left hY hb)
    _ = R := by rw [← add_mul, hab, one_mul]

theorem off_norm_cones_convex {p τ : ℝ} (hp : 1 ≤ p) (hτ : 0 ≤ τ) :
    Convex ℝ {X : Fin 3 → Fin 3 → ℝ |
      ∀ j i, j ≠ i → τ*lpNorm p (X j) ≤ X j i} := by
  intro X hX Y hY a b ha hb hab j i hji
  have hn := (convexOn_lpNorm (ι := Fin 3) (E := ℝ) hp).2
    (Set.mem_univ (X j)) (Set.mem_univ (Y j)) ha hb hab
  have hw := mul_le_mul_of_nonneg_left hn hτ
  have hx := mul_le_mul_of_nonneg_left (hX j i hji) ha
  have hy := mul_le_mul_of_nonneg_left (hY j i hji) hb
  change τ*lpNorm p (a • X j+b • Y j) ≤ a*X j i+b*Y j i
  simp only [smul_eq_mul] at hw
  nlinarith only [hw,hx,hy]

theorem off_sum_norm_cones_convex {p s : ℝ} (hp : 1 ≤ p) (hs : 0 ≤ s) :
    Convex ℝ {X : Fin 3 → Fin 3 → ℝ |
      ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
        s*lpNorm p (X i) ≤ X i j+X i k} := by
  intro X hX Y hY a b ha hb hab i j k hij hik hjk
  have hn := (convexOn_lpNorm (ι := Fin 3) (E := ℝ) hp).2
    (Set.mem_univ (X i)) (Set.mem_univ (Y i)) ha hb hab
  have hw := mul_le_mul_of_nonneg_left hn hs
  have hx := mul_le_mul_of_nonneg_left (hX i j k hij hik hjk) ha
  have hy := mul_le_mul_of_nonneg_left (hY i j k hij hik hjk) hb
  change s*lpNorm p (a • X i+b • Y i) ≤
    (a*X i j+b*Y i j)+(a*X i k+b*Y i k)
  simp only [smul_eq_mul] at hw
  nlinarith only [hw,hx,hy]

theorem convex_retained_localization {p τ s : ℝ}
    (hp : 1 ≤ p) (hτ : 0 ≤ τ) (hs : 0 ≤ s) (R : ℝ) :
    Convex ℝ {X : Fin 3 → Fin 3 → ℝ |
      (∑ j, lpNorm p (X j)) ≤ R ∧
      (∀ j i, j ≠ i → τ*lpNorm p (X j) ≤ X j i) ∧
      (∀ i j k, i ≠ j → i ≠ k → j ≠ k →
        s*lpNorm p (X i) ≤ X i j+X i k)} := by
  exact (norm_sum_budget_convex hp R).inter
    ((off_norm_cones_convex hp hτ).inter (off_sum_norm_cones_convex hp hs))

end HlawkaSchatten.DiagonalCutoff12



theorem solution {p τ s : ℝ}
    (hp : 1 ≤ p) (hτ : 0 ≤ τ) (hs : 0 ≤ s) (R : ℝ) :
    Convex ℝ {X : Fin 3 → Fin 3 → ℝ |
      (∑ j, lpNorm p (X j)) ≤ R ∧
      (∀ j i, j ≠ i → τ*lpNorm p (X j) ≤ X j i) ∧
      (∀ i j k, i ≠ j → i ≠ k → j ≠ k →
        s*lpNorm p (X i) ≤ X i j+X i k)} := by
  exact HlawkaSchatten.DiagonalCutoff12.convex_retained_localization hp hτ hs R

#print axioms solution
