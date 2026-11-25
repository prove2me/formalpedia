-- Prove2me | solution 1 for GroundTheory.PAdicHodge.AInf.map_frobeniusEquiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:49:33.031799+00:00
-- url     : https://prove2.me/submissions/6b125d46-9994-47fa-9a14-ed6419f501ab

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_KerFontaineThetaCompFrobeniusEquivSymmPow
import Definitions.Def_GroundTheory_PAdicHodge_AInfTopology
import Definitions.Def_GroundTheory_PAdicHodge_TiltMap
import Definitions.Def_GroundTheory_PAdicHodge_TiltAlgebra
import Definitions.Def_GroundTheory_PAdicHodge_GaloisOnCp
import Definitions.Def_GroundTheory_PAdicHodge_AInfGalois
import Theorems.Thm_GroundTheory_PAdicHodge_WittVector_frobeniusEquiv_coeff


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
open GroundTheory.PAdicHodge.AInf
variable {K L M : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
  [NontriviallyNormedField L] [IsUltrametricDist L] [NontriviallyNormedField M]
  [IsUltrametricDist M]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p] [IsPerfectoidField L p]
  [IsPerfectoidField M p]
namespace GroundTheory.PAdicHodge.AInf
theorem _root_.solution (φ : K →+* L) (hφ : ∀ x, ‖φ x‖ = ‖x‖) (x : AInf K p) :
    map p φ hφ (WittVector.frobeniusEquiv p _ x) = WittVector.frobeniusEquiv p _ (map p φ hφ x) := by
  refine WittVector.ext fun n => ?_
  rw [map_coeff, WittVector.frobeniusEquiv_coeff, WittVector.frobeniusEquiv_coeff, map_coeff,
    map_pow]
end GroundTheory.PAdicHodge.AInf
