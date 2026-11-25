-- Prove2me | solution 1 for GroundTheory.PAdicHodge.AInf.map_teichmuller
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:49:36.408993+00:00
-- url     : https://prove2.me/submissions/19072833-b97d-4211-bca1-b9db8cd81973

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_KerFontaineThetaCompFrobeniusEquivSymmPow
import Definitions.Def_GroundTheory_PAdicHodge_AInfTopology
import Definitions.Def_GroundTheory_PAdicHodge_TiltMap
import Definitions.Def_GroundTheory_PAdicHodge_TiltAlgebra
import Definitions.Def_GroundTheory_PAdicHodge_GaloisOnCp
import Definitions.Def_GroundTheory_PAdicHodge_AInfGalois

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
theorem _root_.solution (φ : K →+* L) (hφ : ∀ x, ‖φ x‖ = ‖x‖) (x : PreTilt (normInteger K) p) :
    map p φ hφ (WittVector.teichmuller p x) = WittVector.teichmuller p (preTiltMap p φ hφ x) :=
  WittVector.map_teichmuller p _ x
end GroundTheory.PAdicHodge.AInf
