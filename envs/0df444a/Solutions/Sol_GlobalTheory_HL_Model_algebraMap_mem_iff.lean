-- Prove2me | solution 1 for GlobalTheory.HL.Model.algebraMap_mem_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T06:29:19.5812+00:00
-- url     : https://prove2.me/submissions/161645f1-1cea-4951-a7bc-e2eb05140dda

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TorsionBlocks_HermitianLattices
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsIntegralIff
import Theorems.Thm_GlobalTheory_HL_Model_nontrivial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.Model
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
namespace GlobalTheory.HL.Model
theorem _root_.solution (L : LocE F E) (a : F) : algebraMap F E a ∈ L.O ↔ a ∈ 𝒪[F] := by
  have := nontrivial L
  rw [L.O_def, isIntegral_algebraMap_iff (algebraMap F E).injective]
  constructor
  · intro h
    exact (Valuation.integer.integers _).mem_of_integral h
  · intro h
    exact isIntegral_algebraMap (x := (⟨a, h⟩ : 𝒪[F]))
end GlobalTheory.HL.Model
