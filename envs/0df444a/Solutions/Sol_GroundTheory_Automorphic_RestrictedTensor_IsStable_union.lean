-- Prove2me | solution 1 for GroundTheory.Automorphic.RestrictedTensor.IsStable.union
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:46:22.549105+00:00
-- url     : https://prove2.me/submissions/d451ec60-4bd7-45b5-8102-2c6f3c532e93

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Operators

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
open Module
variable {M : Type*} [AddCommGroup M] [Module ℂ M]
namespace GroundTheory.Automorphic.RestrictedTensor
namespace IsStable
theorem _root_.solution {T₁ T₂ : Set (End ℂ M)} {p : Submodule ℂ M} (h₁ : IsStable T₁ p)
    (h₂ : IsStable T₂ p) : IsStable (T₁ ∪ T₂) p := by
  rintro t (ht | ht)
  exacts [h₁ t ht, h₂ t ht]
end IsStable
end GroundTheory.Automorphic.RestrictedTensor
