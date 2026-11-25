-- Prove2me | solution 1 for GroundTheory.Automorphic.Anisotropic.resHom_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:24:59.876473+00:00
-- url     : https://prove2.me/submissions/9c169e6f-4c8a-47b9-a301-bf362ce92b8d

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_AnisotropicRestrict
import Definitions.Def_GroundTheory_AutomorphicForms_AdelicUnitaryGroups
import Definitions.Def_GroundTheory_AutomorphicForms_AnisotropicUnitaryRes

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open Module Matrix TensorProduct
set_option linter.unusedSectionVars false
open GroundTheory GroundTheory.Automorphic
noncomputable section
open GroundTheory.Automorphic.Anisotropic
variable {K E : Type*} [Field K] [CommRing E] [Algebra K E] [Algebra.IsQuadraticExtension K E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {κ : Type*} [Fintype κ] [DecidableEq κ] (b : Basis κ K E)
variable (R : Type*) [CommRing R] [Algebra K R] {R' : Type*} [CommRing R'] [Algebra K R']
local notation "𝒩" => Fintype.card (ι × κ)
namespace GroundTheory.Automorphic.Anisotropic
theorem _root_.solution (M : Matrix ι ι (R ⊗[K] E)) (p q : Fin 𝒩) :
    resHom b R M p q = blockHom b R M ((Fintype.equivFin (ι × κ)).symm p) ((Fintype.equivFin (ι × κ)).symm q) := rfl
end GroundTheory.Automorphic.Anisotropic
