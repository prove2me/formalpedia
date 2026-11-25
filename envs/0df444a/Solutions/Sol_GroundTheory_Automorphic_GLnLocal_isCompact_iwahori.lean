-- Prove2me | solution 1 for GroundTheory.Automorphic.GLnLocal.isCompact_iwahori
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:17:21.562869+00:00
-- url     : https://prove2.me/submissions/34fe3810-dca1-45a0-a813-06a0510f1bd8

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLocal
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLattice
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteBruhat
import Definitions.Def_GroundTheory_AutomorphicForms_AffineBruhat
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_iwahori_le_integralGL
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_isOpen_iwahori
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_isCompact_integralGL


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open Matrix DoubleCoset ValuativeRel
open GroundTheory.Automorphic.GLnLocal
variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  (n : ℕ)
local notation "ϖ" => ((uniformizer F : 𝒪[F]) : F)
namespace GroundTheory.Automorphic.GLnLocal
theorem _root_.solution : IsCompact (iwahori F n : Set (GL (Fin n) F)) :=
  (isCompact_integralGL F n).of_isClosed_subset
    (Subgroup.isClosed_of_isOpen _ (isOpen_iwahori F n)) (iwahori_le_integralGL F n)
end GroundTheory.Automorphic.GLnLocal
