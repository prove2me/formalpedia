-- Prove2me | solution 1 for GroundTheory.LocalField.exists_retraction_adjoin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:48:22.373626+00:00
-- url     : https://prove2.me/submissions/8d5fbd26-6c79-4702-ae78-fb884c63996e

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionInduced
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionIntegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open Module Representation
namespace GroundTheory.LocalField
theorem _root_.solution {ζ : ℂ} (hζ : IsIntegral ℤ ζ) :
    ∃ π : Algebra.adjoin ℤ ({ζ} : Set ℂ) →ₗ[ℤ] ℤ, π 1 = 1 := by
  let pb := Algebra.adjoin.powerBasis' hζ
  have hdim : 0 < pb.dim := pb.dim_pos
  refine ⟨pb.basis.coord ⟨0, hdim⟩, ?_⟩
  have h0 : pb.basis ⟨0, hdim⟩ = 1 := by
    rw [pb.coe_basis]
    simp
  rw [← h0, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_eq_same]
end GroundTheory.LocalField
