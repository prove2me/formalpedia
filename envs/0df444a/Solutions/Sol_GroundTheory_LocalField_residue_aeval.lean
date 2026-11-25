-- Prove2me | solution 1 for GroundTheory.LocalField.residue_aeval
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:01:59.102278+00:00
-- url     : https://prove2.me/submissions/c23de804-dfb8-4ac3-bdb6-9e5c7d612ced

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_Integers
import Definitions.Def_GroundTheory_LocalFields_IntermediateField
import Definitions.Def_GroundTheory_LocalFields_UnramifiedDefs
import Definitions.Def_GroundTheory_LocalFields_UnitsPowers
import Definitions.Def_GroundTheory_LocalFields_UnramifiedHensel

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open ValuativeRel IsLocalRing Polynomial
open scoped _root_.IntermediateField
variable (K M : Type*) [Field K] [ValuativeRel K] [Field M] [ValuativeRel M]
  [Algebra K M] [ValuativeExtension K M]
namespace GroundTheory.LocalField
theorem _root_.solution [Algebra 𝓀[K] 𝓀[M]]
    (h : ∀ x : 𝒪[K], algebraMap 𝓀[K] 𝓀[M] (residue 𝒪[K] x) =
      residue 𝒪[M] (algebraMap 𝒪[K] 𝒪[M] x))
    (P : 𝒪[K][X]) (x : 𝒪[M]) :
    residue 𝒪[M] (aeval x P) = aeval (residue 𝒪[M] x) (P.map (residue 𝒪[K])) := by
  have hc : (algebraMap 𝓀[K] 𝓀[M]).comp (residue 𝒪[K]) =
      (residue 𝒪[M]).comp (algebraMap 𝒪[K] 𝒪[M]) := RingHom.ext h
  rw [aeval_def, aeval_def, eval₂_map, hc, hom_eval₂]
end GroundTheory.LocalField
