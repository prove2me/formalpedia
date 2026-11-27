-- Prove2me | solution 1 for GroundTheory.Automorphic.GJMatrix.measurePreserving_matrixCoordT
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:42:58.628312+00:00
-- url     : https://prove2.me/submissions/e1da8552-48d0-43f2-967c-b3ba7d534381

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_GJMatrixInfinite
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_GJMatrixCoord
import Theorems.Thm_GroundTheory_Automorphic_GJMatrix_measurePreserving_matrixCoord

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
    MeasurePreserving (matrixCoordT : Matrix n n X → n × n → X) (matrixMeasure μ)
      (Measure.pi fun _ : n × n ↦ μ) := by
  have h := (measurePreserving_piCongrLeft (fun _ : n × n ↦ μ) (Equiv.prodComm n n)).comp
    (measurePreserving_matrixCoord (n := n) μ)
  convert h using 1
  funext x p
  simp only [Function.comp_apply, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft,
    MeasurableEquiv.coe_mk, matrixCoordT]
  rfl
end GroundTheory.Automorphic.GJMatrix
