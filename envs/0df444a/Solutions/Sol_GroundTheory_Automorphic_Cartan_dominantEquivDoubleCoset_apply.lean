-- Prove2me | solution 1 for GroundTheory.Automorphic.Cartan.dominantEquivDoubleCoset_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:37:03.15409+00:00
-- url     : https://prove2.me/submissions/81f5c9ab-f6c5-4289-a1b3-a752d233c9f2

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLattice
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_MulLeftCancelOfDetNeZero
import Definitions.Def_GroundTheory_AutomorphicForms_Cartan

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
open Matrix
open GroundTheory.Automorphic.Cartan
open ValuativeRel GLnLocal DoubleCoset
variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  (n : ℕ)
namespace GroundTheory.Automorphic.Cartan
theorem _root_.solution (μ : {μ : Fin n → ℤ // IsDominant μ}) :
    dominantEquivDoubleCoset F n μ =
      DoubleCoset.mk (integralGL F n) (integralGL F n) (diagPow F n μ) :=
  rfl
end GroundTheory.Automorphic.Cartan
