-- Prove2me | solution 1 for GroundTheory.Automorphic.GJMatrix.measurePreserving_matrixCoord
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:09:17.840887+00:00
-- url     : https://prove2.me/submissions/0947f1c7-c001-49ee-be84-fb5bde477005

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_GJMatrixInfinite
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_GJMatrixCoord
import Theorems.Thm_GroundTheory_Automorphic_GJMatrix_measurePreserving_curry_symm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix
open MeasureTheory Matrix
noncomputable section
variable {n X : Type*} [Fintype n]
namespace GroundTheory.Automorphic.GJMatrix
theorem _root_.solution [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ] :
    MeasurePreserving (matrixCoord : Matrix n n X → n × n → X) (matrixMeasure μ)
      (Measure.pi fun _ : n × n ↦ μ) :=
  measurePreserving_curry_symm μ
end GroundTheory.Automorphic.GJMatrix
