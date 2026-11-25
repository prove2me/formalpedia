-- Prove2me | solution 1 for GroundTheory.Automorphic.Anisotropic.trHom_val
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:28:16.11713+00:00
-- url     : https://prove2.me/submissions/c40332ef-6d67-45d5-bfd2-4f4837424128

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
variable {R}
variable (R)
namespace GroundTheory.Automorphic.Anisotropic
theorem _root_.solution (g : GL ι (R ⊗[K] E)) :
    (trHom b R g : Matrix (Fin 𝒩) (Fin 𝒩) R) = resHom b R ((↑g⁻¹ : Matrix ι ι (R ⊗[K] E))ᵀ) := rfl
end GroundTheory.Automorphic.Anisotropic
