-- Prove2me | solution 2 for Neutral.B1.equivariant_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:49:31.37294+00:00
-- url     : https://prove2.me/submissions/e9f30ec8-f97d-492f-b218-03aab641cf22

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
namespace Neutral.B1
theorem _root_.solution {R Γ M : Type*} [CommRing R] [Group Γ] [AddCommGroup M] [Module R M]
    (rho : Representation R Γ M) (c : R) :
    ∀ g m, (c • LinearMap.id : M →ₗ[R] M) (rho g m) = rho g ((c • LinearMap.id : M →ₗ[R] M) m) := by
  intro g m
  simp
end Neutral.B1
