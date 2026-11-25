-- Prove2me | solution 1 for GroundTheory.PAdicHodge.towerCoeff_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:23:21.177813+00:00
-- url     : https://prove2.me/submissions/2ec2ab08-df3e-4a33-aef8-ff2325bd82a6

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_NormalizedTrace
import Definitions.Def_GroundTheory_PAdicHodge_CyclotomicField
import Definitions.Def_GroundTheory_PAdicHodge_NormalizedTraceTower
import Theorems.Thm_GroundTheory_PAdicHodge_normTrace_mem


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.PAdicHodge
open IntermediateField Polynomial Module
noncomputable section
variable {p : ℕ} [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))
variable [FiniteDimensional ℚ_[p] K]
namespace GroundTheory.PAdicHodge
theorem _root_.solution (m : ℕ) (y : PadicAlgCl p) (i : Fin (relDeg K (stableIndex K))) :
    towerCoeff K m y i ∈ cycl p m :=
  mul_mem (IntermediateField.natCast_mem _ _) (normTrace_mem _ _)
end GroundTheory.PAdicHodge
