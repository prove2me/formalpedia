-- Prove2me | solution 1 for GroundTheory.Automorphic.GLnLocal.isLocallyProfinite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:43:22.070925+00:00
-- url     : https://prove2.me/submissions/9e2917de-0797-4941-b759-1ad36153a21f

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLocal

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
open ValuativeRel Topology Filter Set
open GroundTheory.Automorphic.GLnLocal
variable (F : Type*) [Field F] [ValuativeRel F] (n : ℕ)
variable [TopologicalSpace F] [IsNonarchimedeanLocalField F]
namespace GroundTheory.Automorphic.GLnLocal
theorem _root_.solution :
    IsTopologicalGroup (GL (Fin n) F) ∧ LocallyCompactSpace (GL (Fin n) F) ∧
      T2Space (GL (Fin n) F) ∧ TotallyDisconnectedSpace (GL (Fin n) F) :=
  ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩
end GroundTheory.Automorphic.GLnLocal
