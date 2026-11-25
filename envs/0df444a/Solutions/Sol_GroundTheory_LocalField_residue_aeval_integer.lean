-- Prove2me | solution 1 for GroundTheory.LocalField.residue_aeval_integer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:18:51.145925+00:00
-- url     : https://prove2.me/submissions/3ad8675a-d8db-4531-bb51-67cb87d66af3

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Eisenstein
import Definitions.Def_GroundTheory_LocalFields_Monogenic

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
open ValuativeRel Polynomial IsDiscreteValuationRing IsLocalRing
variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
namespace GroundTheory.LocalField
theorem _root_.solution (p : 𝒪[K][X]) (x : 𝒪[L]) :
    residue 𝒪[L] (aeval x p) = aeval (residue 𝒪[L] x) (p.map (residue 𝒪[K])) := by
  rw [aeval_def, aeval_def, eval₂_map, hom_eval₂]
  congr 1
end GroundTheory.LocalField
