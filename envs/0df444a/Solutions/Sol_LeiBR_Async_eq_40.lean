-- Prove2me | solution 1 for LeiBR.Async.eq_40
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T11:09:44.269638+00:00
-- url     : https://prove2.me/submissions/754aea30-5937-431d-85aa-de874f5ed1c5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_LeiBR_Async_Game
import Definitions.Def_LeiBR_Async_Model
import Theorems.Thm_LeiBR_Async_eq_5
import Theorems.Thm_LeiBR_Async_fixed_point

open MeasureTheory

open LeiBR.Async in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {N : ℕ} {n : Fin N → ℕ} (X : ∀ i, Set (LeiBR.Sync.Strat n i)) (f : Fin N → LeiBR.Sync.Profile n → ℝ)
    (hA1 : Assumption1ab X f) (μ : ℝ) (hμ : 0 < μ) (xhat : LeiBR.Sync.Profile n → LeiBR.Sync.Profile n)
    (hxhat : LeiBR.Sync.IsProxBR X f μ xhat) (xs : LeiBR.Sync.Profile n) (hNE : LeiBR.Sync.IsNashEq X f xs)
    (y : Ω → LeiBR.Sync.Profile n) (hy : Measurable y) (hyX : ∀ ω, y ω ∈ profileSet X) (i : Fin N) :
    ∫ ω, ‖xhat (y ω) i - xs i‖ ∂P = ∫ ω, ‖xhat (y ω) i - xhat xs i‖ ∂P ∧
      ∫ ω, ‖xhat (y ω) i - xhat xs i‖ ∂P ≤
        normInf (LeiBR.Sync.Gamma X f μ) * ⨆ j, ∫ ω, ‖y ω j - xs j‖ ∂P := by
  classical
  have hfp := fixed_point X f hA1 μ hμ xhat hxhat xs hNE i
  refine ⟨by rw [hfp], ?_⟩
  have hxsX : xs ∈ profileSet X := hNE.1
  have hlip : LipschitzOnWith (∑ j, ‖LeiBR.Sync.Gamma X f μ i j‖₊) (fun z => xhat z i)
      (profileSet X) := by
    refine LipschitzOnWith.of_dist_le_mul fun a ha b hb => ?_
    rw [dist_eq_norm, dist_eq_norm]
    refine (eq_5 X f hA1 μ hμ xhat hxhat b hb a ha i).trans ?_
    push_cast
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun j _ => ?_
    have h1 : ‖a j - b j‖ ≤ ‖a - b‖ := norm_le_pi_norm (a - b) j
    calc LeiBR.Sync.Gamma X f μ i j * ‖a j - b j‖ ≤ ‖LeiBR.Sync.Gamma X f μ i j‖ * ‖a j - b j‖ :=
          mul_le_mul_of_nonneg_right (Real.le_norm_self _) (norm_nonneg _)
      _ ≤ ‖LeiBR.Sync.Gamma X f μ i j‖ * ‖a - b‖ :=
          mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
  have hg : Measurable (fun ω => xhat (y ω) i) := by
    have hc : Continuous (fun z : profileSet X => xhat (z : LeiBR.Sync.Profile n) i) :=
      hlip.continuousOn.domRestrict
    exact hc.measurable.comp (hy.subtype_mk (h := hyX))
  have hmemj : ∀ ω j, y ω j ∈ X j := by
    intro ω j
    have := hyX ω
    simp only [profileSet, Set.mem_univ_pi] at this
    exact this j
  have hxsj : ∀ j, xs j ∈ X j := fun j => hNE.1 j (Set.mem_univ j)
  have hintj : ∀ j, Integrable (fun ω => ‖y ω j - xs j‖) P := by
    intro j
    refine Integrable.of_bound (C := Metric.diam (X j))
      (((measurable_pi_apply j).comp hy).sub_const _).norm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [norm_norm, ← dist_eq_norm]
    exact Metric.dist_le_diam_of_mem (hA1.compact j).isBounded (hmemj ω j) (hxsj j)
  have hint : Integrable (fun ω => ‖xhat (y ω) i - xhat xs i‖) P := by
    refine Integrable.of_bound (C := Metric.diam (X i)) (hg.sub_const _).norm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [norm_norm, ← dist_eq_norm]
    exact Metric.dist_le_diam_of_mem (hA1.compact i).isBounded (hxhat (y ω) (hyX ω) i).1
      (hxhat xs hxsX i).1
  have hsumint : Integrable (fun ω => ∑ j, ‖LeiBR.Sync.Gamma X f μ i j‖ * ‖y ω j - xs j‖) P :=
    integrable_finset_sum _ fun j _ => (hintj j).const_mul _
  have hbdd : BddAbove (Set.range fun j => ∫ ω, ‖y ω j - xs j‖ ∂P) := Set.finite_range _ |>.bddAbove
  have hrow : ∑ j, ‖LeiBR.Sync.Gamma X f μ i j‖ ≤ normInf (LeiBR.Sync.Gamma X f μ) := by
    unfold normInf
    have : (∑ j, ‖LeiBR.Sync.Gamma X f μ i j‖₊ : NNReal) ≤
        Finset.univ.sup fun i' => ∑ j, ‖LeiBR.Sync.Gamma X f μ i' j‖₊ :=
      Finset.le_sup (f := fun i' => ∑ j, ‖LeiBR.Sync.Gamma X f μ i' j‖₊) (Finset.mem_univ i)
    have := NNReal.coe_le_coe.mpr this
    push_cast at this
    exact this
  calc ∫ ω, ‖xhat (y ω) i - xhat xs i‖ ∂P
      ≤ ∫ ω, ∑ j, ‖LeiBR.Sync.Gamma X f μ i j‖ * ‖y ω j - xs j‖ ∂P := by
        refine integral_mono hint hsumint fun ω => ?_
        refine (eq_5 X f hA1 μ hμ xhat hxhat xs hxsX (y ω) (hyX ω) i).trans ?_
        exact Finset.sum_le_sum fun j _ =>
          mul_le_mul_of_nonneg_right (Real.le_norm_self _) (norm_nonneg _)
    _ = ∑ j, ‖LeiBR.Sync.Gamma X f μ i j‖ * ∫ ω, ‖y ω j - xs j‖ ∂P := by
        rw [integral_finset_sum _ fun j _ => (hintj j).const_mul _]
        simp_rw [integral_const_mul]
    _ ≤ ∑ j, ‖LeiBR.Sync.Gamma X f μ i j‖ * ⨆ j', ∫ ω, ‖y ω j' - xs j'‖ ∂P :=
        Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (le_ciSup hbdd j) (norm_nonneg _)
    _ = (∑ j, ‖LeiBR.Sync.Gamma X f μ i j‖) * ⨆ j', ∫ ω, ‖y ω j' - xs j'‖ ∂P := by
        rw [Finset.sum_mul]
    _ ≤ normInf (LeiBR.Sync.Gamma X f μ) * ⨆ j', ∫ ω, ‖y ω j' - xs j'‖ ∂P := by
        refine mul_le_mul_of_nonneg_right hrow ?_
        exact (integral_nonneg fun ω => norm_nonneg _).trans (le_ciSup hbdd i)
