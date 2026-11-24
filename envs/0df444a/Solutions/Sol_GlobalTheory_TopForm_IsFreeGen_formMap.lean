-- Prove2me | solution 1 for GlobalTheory.TopForm.IsFreeGen.formMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:41:24.316596+00:00
-- url     : https://prove2.me/submissions/1b73c3a3-336d-4388-8d4c-cae440577b1f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_AlternatingMapSumSmulEqDetSmul
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExistsAlgHomOfIsBaseChange
import Theorems.Thm_GlobalTheory_TopForm_isBaseChange_exteriorPower
import Theorems.Thm_GlobalTheory_TopForm_IsFreeGen_of_isBaseChange

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open scoped TensorProduct
open GlobalTheory
open GlobalTheory.TopForm
variable {k A B C : Type*} [CommRing k] [CommRing A] [CommRing B] [CommRing C]
variable {D : ℕ}
variable {α : k →+* A} {β : k →+* B} {γ : k →+* C}
namespace GlobalTheory.TopForm
namespace IsFreeGen
theorem _root_.solution {ρ : A →+* B} (hρ : ρ.Etale) (h : ρ.comp α = β) {ω : Forms α D}
    (hω : IsFreeGen A ω) : IsFreeGen B (formMap D ρ h ω) := by
  letI := α.toAlgebra
  letI := β.toAlgebra
  letI := ρ.toAlgebra
  haveI : IsScalarTower k A B := IsScalarTower.of_algebraMap_eq' h.symm
  haveI : Algebra.Etale A B := hρ
  exact hω.of_isBaseChange (isBaseChange_exteriorPower
    (KaehlerDifferential.isBaseChange_of_formallyEtale k A B) D)
end IsFreeGen
end GlobalTheory.TopForm
