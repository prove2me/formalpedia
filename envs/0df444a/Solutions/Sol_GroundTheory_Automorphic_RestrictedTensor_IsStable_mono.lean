-- Prove2me | solution 1 for GroundTheory.Automorphic.RestrictedTensor.IsStable.mono
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:43:44.690513+00:00
-- url     : https://prove2.me/submissions/5d29e134-e5ae-4f52-86f0-d1995e1a66b8

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
theorem _root_.solution {T₁ T₂ : Set (End ℂ M)} {p : Submodule ℂ M} (h : IsStable T₂ p)
    (hT : T₁ ⊆ T₂) : IsStable T₁ p :=
  fun t ht => h t (hT ht)
end IsStable
end GroundTheory.Automorphic.RestrictedTensor
