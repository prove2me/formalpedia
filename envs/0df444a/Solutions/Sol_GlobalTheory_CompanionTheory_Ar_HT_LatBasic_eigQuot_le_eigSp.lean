-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.HT.LatBasic.eigQuot_le_eigSp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:35:27.552133+00:00
-- url     : https://prove2.me/submissions/bbedfaa9-f095-4a18-8a85-b0375e005fbd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LogAbsVpOfNormalised
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_IdemDen
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_CommutativeAlgebra_LatNormGrLatNeZeroOfSpan
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_HT_LatBasic_eigProj_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.HT
open Module NumberField
open GlobalTheory.CompanionTheory.Ar.HT.LatBasic
open TensorProduct
variable {A : Type} [CommRing A] {K : Type} [Field K] [Algebra A K]
  {V : Type} [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower A K V]
  {E : Type} [Field E] [NumberField E]
namespace GlobalTheory.CompanionTheory.Ar.HT.LatBasic
theorem _root_.solution (ρ : 𝓞 E →+* Module.End K V) (σ : E →+* K) (X : Submodule A V) :
    eigQuot ρ σ X ≤ (eigSp ρ σ).restrictScalars A := by
  rintro _ ⟨x, -, rfl⟩
  exact eigProj_mem ρ σ x
end GlobalTheory.CompanionTheory.Ar.HT.LatBasic
