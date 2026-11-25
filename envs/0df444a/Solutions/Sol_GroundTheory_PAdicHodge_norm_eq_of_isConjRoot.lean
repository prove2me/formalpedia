-- Prove2me | solution 1 for GroundTheory.PAdicHodge.norm_eq_of_isConjRoot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:19:04.166929+00:00
-- url     : https://prove2.me/submissions/7e1c513f-1376-4215-88e3-ddeeaeef30c8

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_TiltAlgebra
import Definitions.Def_GroundTheory_PAdicHodge_AxLemma
import Definitions.Def_GroundTheory_PAdicHodge_UntiltApproxLemmas

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
open Polynomial
variable {F E : Type*} [NontriviallyNormedField F] [CompleteSpace F] [IsUltrametricDist F]
  [NormedField E] [NormedAlgebra F E]
namespace GroundTheory.PAdicHodge
theorem _root_.solution {x x' : E} (hx : IsIntegral F x) (h : IsConjRoot F x x') :
    ‖x‖ = ‖x'‖ := by
  have hx' : IsIntegral F x' := h.isIntegral hx
  have e1 := NormedAlgebra.norm_eq_spectralNorm F (⟨x, hx⟩ : algebraicClosure F E)
  have e2 := NormedAlgebra.norm_eq_spectralNorm F (⟨x', hx'⟩ : algebraicClosure F E)
  change ‖x‖ = _ at e1
  change ‖x'‖ = _ at e2
  rw [e1, e2, spectralNorm, spectralNorm, IntermediateField.minpoly_eq,
    IntermediateField.minpoly_eq]
  change spectralValue (minpoly F x) = spectralValue (minpoly F x')
  rw [h]
end GroundTheory.PAdicHodge
