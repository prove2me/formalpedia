-- Prove2me | solution 1 for GroundTheory.Automorphic.GJMatrix.measurePreserving_curry_symm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:47:10.863555+00:00
-- url     : https://prove2.me/submissions/8159e9ef-57a7-4229-9280-6d8d5356facb

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_TraceLatticePoisson
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_GJMatrixInfinite

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix
open GroundTheory.Global NumberField NumberField.mixedEmbedding MeasureTheory Module Filter
open scoped FourierTransform SchwartzMap RealInnerProductSpace nonZeroDivisors Classical
set_option synthInstance.maxSize 1000
noncomputable section
namespace GroundTheory.Automorphic.GJMatrix
theorem _root_.solution {α κ X : Type*} [Fintype α] [Fintype κ] [MeasurableSpace X]
    (μ : Measure X) [SigmaFinite μ] :
    MeasurePreserving (MeasurableEquiv.curry α κ X).symm
      (Measure.pi fun _ : α ↦ Measure.pi fun _ : κ ↦ μ) (Measure.pi fun _ : α × κ ↦ μ) := by
  refine ⟨(MeasurableEquiv.curry α κ X).symm.measurable, ?_⟩
  refine (Measure.pi_eq (μ := fun _ : α × κ ↦ μ) fun s hs ↦ ?_).symm
  rw [MeasurableEquiv.map_apply]
  have h : (MeasurableEquiv.curry α κ X).symm ⁻¹' Set.univ.pi s =
      Set.univ.pi fun a ↦ Set.univ.pi fun k ↦ s (a, k) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Prod.forall]
    rfl
  rw [h, Measure.pi_pi]
  simp_rw [Measure.pi_pi]
  rw [← Fintype.prod_prod_type']
end GroundTheory.Automorphic.GJMatrix
