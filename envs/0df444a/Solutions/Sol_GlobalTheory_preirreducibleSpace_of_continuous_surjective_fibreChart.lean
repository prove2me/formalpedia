-- Prove2me | solution 1 for GlobalTheory.preirreducibleSpace_of_continuous_surjective_fibreChart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:29:49.760777+00:00
-- url     : https://prove2.me/submissions/a385b521-66f7-4fdf-a93d-20aa797043f9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HypersurfacePartGeometricIrreducibleSpreadsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_StandardEtaleMvPolynomialHypersurfaceStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PreirreducibleSpaceFibreHypersurfaceSpectrumIffStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PreirreducibleFibreStandardEtaleSpreads

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
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [hX : PreirreducibleSpace X] (f : X → Y) (hf : Continuous f)
    (hs : Function.Surjective f) : PreirreducibleSpace Y :=
  ⟨by simpa [Set.image_univ_of_surjective hs] using
    hX.isPreirreducible_univ.image f hf.continuousOn⟩
end GlobalTheory
