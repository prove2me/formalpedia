-- Prove2me | solution 1 for GlobalTheory.CommonDenominator.algebraMap_mem_O
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:24:16.121818+00:00
-- url     : https://prove2.me/submissions/de40bc49-6ade-4039-97b5-133021ca5067

import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_AlgebraMapMemO

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel
open GlobalTheory GlobalTheory.CommonDenominator
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
namespace GlobalTheory.CommonDenominator
theorem _root_.solution (L : Formalism.MainNotions.S.Loc.LocE F E) (t : 𝒪[F]) :
    algebraMap F E (t : F) ∈ L.O := by
  rw [L.O_def]
  have h : algebraMap F E (t : F) = algebraMap 𝒪[F] E t := by
    rw [IsScalarTower.algebraMap_apply 𝒪[F] F E]; rfl
  rw [h]
  exact isIntegral_algebraMap
end GlobalTheory.CommonDenominator
