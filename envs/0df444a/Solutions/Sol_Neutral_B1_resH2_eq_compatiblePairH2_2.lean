-- Prove2me | solution 2 for Neutral.B1.resH2_eq_compatiblePairH2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:50:36.132388+00:00
-- url     : https://prove2.me/submissions/12552241-b89f-4678-a711-548cd78683e6

import Mathlib
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_Reciprocity
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_Duality

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Representation
open Neutral Neutral.B1
set_option linter.unusedVariables false
noncomputable section
open Representation
variable {R : Type*} [CommRing R]
variable {G : Type*} [Group G] [TopologicalSpace G]
variable {M : Type*} [AddCommGroup M] [Module R M] [TopologicalSpace M]
  [IsTopologicalAddGroup M] [ContinuousConstSMul R M]
variable (rho : Representation R G M)
namespace Neutral.B1
theorem _root_.solution {H : Type*} [Group H] [TopologicalSpace H] (phi : H →* G)
    (hphi : Continuous phi) :
    resH2 rho phi hphi =
      compatiblePairH2 rho (rho.comp phi) phi hphi LinearMap.id continuous_id (fun _ _ => rfl) :=
  Submodule.linearMap_qext _ (LinearMap.ext fun _ => rfl)
end Neutral.B1
