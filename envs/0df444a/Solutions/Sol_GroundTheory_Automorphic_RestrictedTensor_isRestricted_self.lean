-- Prove2me | solution 1 for GroundTheory.Automorphic.RestrictedTensor.isRestricted_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:59:29.220267+00:00
-- url     : https://prove2.me/submissions/110271ff-ef87-4583-9fb1-372495c59422

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRep
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Restricted

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
open GroundTheory.Automorphic.RestrictedTensor
open PiTensorProduct Filter Function Module Set
open scoped TensorProduct RestrictedProduct
variable {ι : Type*} {V : ι → Type*} [∀ v, AddCommGroup (V v)] [∀ v, Module ℂ (V v)]
namespace GroundTheory.Automorphic.RestrictedTensor
theorem _root_.solution (ξ : ∀ v, V v) : IsRestricted ξ ξ :=
  Eventually.of_forall fun _ => rfl
end GroundTheory.Automorphic.RestrictedTensor
