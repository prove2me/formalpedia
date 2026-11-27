-- Prove2me | solution 1 for GroundTheory.Automorphic.Anisotropic.resVec_vecMul_trHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:45:40.5409+00:00
-- url     : https://prove2.me/submissions/75037089-9c49-401d-a446-876aede49c35

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_AnisotropicRestrict
import Definitions.Def_GroundTheory_AutomorphicForms_AdelicUnitaryGroups
import Definitions.Def_GroundTheory_AutomorphicForms_AnisotropicUnitaryRes
import Theorems.Thm_GroundTheory_Automorphic_Anisotropic_resVec_vecMul
import Theorems.Thm_GroundTheory_Automorphic_Anisotropic_trHom_val

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
theorem _root_.solution (x : ι → R ⊗[K] E) (g : GL ι (R ⊗[K] E)) :
    resVec b R x ᵥ* (trHom b R g : Matrix (Fin 𝒩) (Fin 𝒩) R) =
      resVec b R ((↑g⁻¹ : Matrix ι ι (R ⊗[K] E)) *ᵥ x) := by
  rw [trHom_val, ← resVec_vecMul, vecMul_transpose]
end GroundTheory.Automorphic.Anisotropic
