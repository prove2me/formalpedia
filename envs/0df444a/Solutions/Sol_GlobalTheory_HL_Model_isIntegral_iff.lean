-- Prove2me | solution 1 for GlobalTheory.HL.Model.isIntegral_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:40:34.410751+00:00
-- url     : https://prove2.me/submissions/5ceb6e2d-3f0c-42da-a94c-eb9e23b4c47a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TorsionBlocks_HermitianLattices
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsIntegralIff

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
theorem _root_.solution (a : F) : IsIntegral 𝒪[F] a ↔ a ∈ 𝒪[F] := by
  constructor
  · intro h
    exact (Valuation.integer.integers _).mem_of_integral h
  · intro h
    exact isIntegral_algebraMap (x := (⟨a, h⟩ : 𝒪[F]))
end GlobalTheory.HL.Model
