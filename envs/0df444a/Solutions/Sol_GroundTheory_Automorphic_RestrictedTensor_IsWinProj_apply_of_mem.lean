-- Prove2me | solution 1 for GroundTheory.Automorphic.RestrictedTensor.IsWinProj.apply_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:48:33.222499+00:00
-- url     : https://prove2.me/submissions/de5bdcf2-a1b3-474b-8bca-415887542395

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Operators
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_GenWindow

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
open Module Set
variable {M : Type*} [Monoid M] {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
  [Module ℂ W]
variable (ρ : Representation ℂ M V)
variable {ρ} {e : End ℂ V}
namespace GroundTheory.Automorphic.RestrictedTensor
namespace IsWinProj
theorem _root_.solution (he : IsWinProj ρ e) {v : V} (hv : v ∈ LinearMap.range e) :
    e v = v := by
  obtain ⟨w, rfl⟩ := hv
  exact he.idem w
end IsWinProj
end GroundTheory.Automorphic.RestrictedTensor
