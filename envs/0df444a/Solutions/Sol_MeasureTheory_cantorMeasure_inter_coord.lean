-- Prove2me | solution 1 for MeasureTheory.cantorMeasure_inter_coord
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:35:56.832545+00:00
-- url     : https://prove2.me/submissions/86a0589a-09fc-44b6-97d5-5dcc599d941e

module
public import Definitions.Def_AddUN_UniversallyNull
public import Mathlib.MeasureTheory.Measure.Regular
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.Topology.ClopenBox
public import Definitions.Def_AddUN_CantorMeasure
public import Theorems.Thm_MeasureTheory_flip_apply_self
public import Theorems.Thm_MeasureTheory_flip_flip
public import Theorems.Thm_MeasureTheory_measurePreserving_flip
public import Theorems.Thm_MeasureTheory_measurableEmbedding_flip
attribute [local simp] MeasureTheory.flip_apply_self
attribute [local simp] MeasureTheory.flip_flip

set_option autoImplicit false
@[expose] public section
public section
open Set Filter Topology TopologicalSpace
open scoped ENNReal
open MeasureTheory
namespace MeasureTheory
theorem _root_.solution {E : Set (ℕ → Bool)} {i : ℕ} (hflip : flip i ⁻¹' E = E)
    (b : Bool) : cantorMeasure (E ∩ {w | w i = b}) = cantorMeasure E / 2 := by
  have hmeas : ∀ b : Bool, MeasurableSet {w : ℕ → Bool | w i = b} := fun b ↦
    measurableSet_eq_fun (measurable_pi_apply i) measurable_const
  have hpre : flip i ⁻¹' (E ∩ {w | w i = !b}) = E ∩ {w | w i = b} := by
    rw [preimage_inter, hflip]
    ext w
    cases b <;> simp
  have heq : cantorMeasure (E ∩ {w | w i = b}) = cantorMeasure (E ∩ {w | w i = !b}) := by
    rw [← hpre]
    exact (measurePreserving_flip i).measure_preimage_emb (measurableEmbedding_flip i) _
  have hdiff : E \ {w | w i = b} = E ∩ {w | w i = !b} := by
    ext w
    cases b <;> simp
  have hsum := measure_inter_add_sdiff (μ := cantorMeasure) E (hmeas b)
  rw [hdiff, ← heq, ← two_mul] at hsum
  rw [ENNReal.eq_div_iff (by norm_num) (by norm_num)]
  exact hsum
end MeasureTheory
