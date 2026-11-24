-- Prove2me | solution 1 for GlobalTheory.FibreHyp.preirreducibleSpace_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:51:33.63018+00:00
-- url     : https://prove2.me/submissions/b55acf64-d9b1-4e65-9dc0-39283f735cc0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PreirreducibleSpaceFibreHypersurfaceSpectrumIff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj
noncomputable section
open GlobalTheory GlobalTheory.FibreHyp
namespace GlobalTheory.FibreHyp
theorem _root_.solution {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) :
    PreirreducibleSpace X ↔ PreirreducibleSpace Y := by
  have key : ∀ {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y),
      PreirreducibleSpace X → PreirreducibleSpace Y := by
    intro X Y _ _ e h
    refine ⟨?_⟩
    have := (PreirreducibleSpace.isPreirreducible_univ (X := X)).image e e.continuous.continuousOn
    rwa [Set.image_univ_of_surjective e.surjective] at this
  exact ⟨key e, key e.symm⟩
end GlobalTheory.FibreHyp
