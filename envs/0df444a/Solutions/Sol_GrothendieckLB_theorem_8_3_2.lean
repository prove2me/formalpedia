-- Prove2me | solution 2 for GrothendieckLB.theorem_8_3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T15:48:59.297205+00:00
-- url     : https://prove2.me/submissions/3df419d0-6878-4ddc-8780-a7cbcb14bce9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_GrothendieckLB_cubic_positivePart_gaussian_bound
import Definitions.Def_GrothendieckLB_IsTernaryFn
import Definitions.Def_GrothendieckLB_V
import Definitions.Def_GrothendieckLB_beta

open MeasureTheory ProbabilityTheory GrothendieckLB

private noncomputable abbrev normalMeasure : Measure ℝ := gaussianReal 0 1

private lemma expectation_eq (f : ℝ → ℝ) :
    stdExp f = ∫ z, f z ∂normalMeasure := by
  rw [integral_gaussianReal_eq_integral_smul one_ne_zero]
  simp only [stdExp, smul_eq_mul]
  exact integral_congr_ae (Filter.Eventually.of_forall fun z => mul_comm _ _)

private lemma hermite_integrable (j : Fin 4) : Integrable (he j) normalMeasure := by
  have hp (n : ℕ) : Integrable (fun z : ℝ => z ^ n) normalMeasure := by
    have hm : MemLp (id : ℝ → ℝ) (n : ENNReal) normalMeasure :=
      memLp_id_gaussianReal' _ (by simp)
    apply (integrable_norm_iff (by fun_prop)).mp
    simpa only [norm_pow, id_eq] using hm.integrable_norm_pow'
  have hid : Integrable (fun z : ℝ => z) normalMeasure := IsGaussian.integrable_id
  fin_cases j
  · exact integrable_const 1
  · exact hid
  · exact ((hp 2).sub (integrable_const 1)).div_const _
  · exact ((hp 3).sub (hid.const_mul 3)).div_const _

private lemma price_le_positivePart {v : ℝ} (hv : v = 1 ∨ v = 0 ∨ v = -1)
    (p w : ℝ) : v * p - w * v ^ 2 ≤ max 0 (|p| - w) := by
  rcases hv with rfl | rfl | rfl
  · simpa using (sub_le_sub_right (le_abs_self p) w).trans (le_max_right 0 _)
  · simp
  · simpa using (sub_le_sub_right (neg_le_abs p) w).trans (le_max_right 0 _)

theorem solution {u : ℝ → ℝ} (hu : IsTernaryFn u) :
    V u ≤ 3 * ABPOnline.cG * beta u - beta u ^ 2 := by
  let m (j : Fin 4) := stdExp fun z => u z * he j z
  let R := 3 * ABPOnline.cG / 2
  let c := R - beta u
  let p (z : ℝ) := ∑ j, m j * he j z
  have hbound (z) : ‖u z‖ ≤ 1 := by
    rcases hu.2 z with h | h | h <;> simp [h]
  have hterm (j) : Integrable (fun z => m j * (u z * he j z)) normalMeasure :=
    ((hermite_integrable j).bdd_mul hu.1.aestronglyMeasurable
      (Filter.Eventually.of_forall hbound)).const_mul _
  have hp : Integrable p normalMeasure := integrable_finsetSum _ fun j _ =>
    (hermite_integrable j).const_mul (m j)
  have habs : Integrable (fun z : ℝ => |z|) normalMeasure := IsGaussian.integrable_id.abs
  have hbudget : Integrable (fun z => |z| * u z ^ 2) normalMeasure := by
    apply habs.mul_bdd (hu.1.pow_const 2).aestronglyMeasurable (c := 1)
    exact Filter.Eventually.of_forall fun z => by
      rcases hu.2 z with h | h | h <;> simp [h]
  have hmass : (∫ z, ∑ j, m j * (u z * he j z) ∂normalMeasure) = V u := by
    rw [integral_finsetSum _ (fun j _ => hterm j)]
    apply Finset.sum_congr rfl
    intro j _
    rw [integral_const_mul, ← expectation_eq]
    change m j * m j = m j ^ 2
    ring
  have hcost : (∫ z, c * (|z| * u z ^ 2) ∂normalMeasure) = c * beta u := by
    rw [integral_const_mul, ← expectation_eq] <;> rfl
  have hpriced : V u - c * beta u ≤ stdExp (fun z => max 0 (|p z| - c * |z|)) := by
    rw [← hmass, ← hcost, ← integral_sub (integrable_finsetSum _ (fun j _ => hterm j))
      (hbudget.const_mul c), expectation_eq]
    apply integral_mono ((integrable_finsetSum _ (fun j _ => hterm j)).sub (hbudget.const_mul c))
      ((integrable_const (0 : ℝ)).sup (hp.abs.sub (habs.const_mul c)))
    intro z
    change (∑ j, m j * (u z * he j z)) - c * (|z| * u z ^ 2) ≤
      max 0 (|p z| - c * |z|)
    have hfactor : (∑ j, m j * (u z * he j z)) = u z * p z := by
      rw [show p z = ∑ j, m j * he j z from rfl, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [hfactor, ← mul_assoc]
    exact price_le_positivePart (hu.2 z) (p z) (c * |z|)
  have hdual := cubic_positivePart_gaussian_bound m c
  change stdExp (fun z => max 0 (|p z| - c * |z|)) ≤ R * (Real.sqrt (V u + c ^ 2) - c) at hdual
  have hR : 0 ≤ R := by dsimp [R, ABPOnline.cG]; positivity
  have hq : 0 ≤ V u + c ^ 2 :=
    add_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _) (sq_nonneg _)
  have hs := Real.sq_sqrt hq
  have hr : Real.sqrt (V u + c ^ 2) ≤ R := by
    by_contra! hlarge
    have hprod := mul_pos (sub_pos.mpr hlarge) (lt_of_le_of_lt hR hlarge)
    have h := hpriced.trans hdual
    dsimp only [c] at h hs hprod
    nlinarith only [h, hs, hprod]
  have hsquare := mul_self_le_mul_self (Real.sqrt_nonneg _) hr
  rw [← sq, hs] at hsquare
  dsimp only [c, R] at hsquare
  nlinarith only [hsquare]
