-- Prove2me | solution 1 for GlobalTheory.SgLoc.Top.locE_homeo
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:03:52.031479+00:00
-- url     : https://prove2.me/submissions/e2375171-722f-4892-a824-509d3986d5e6

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_RowRawRange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_T2SpaceOfIsNonarchimedeanLocalFieldFlagMeasures

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel MeasureTheory Formalism.MainNotions.S.Loc
open GlobalTheory GlobalTheory.SgLoc GlobalTheory.SgLoc.Top
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
namespace GlobalTheory.SgLoc.Top
theorem _root_.solution [IsNonarchimedeanLocalField F] (L : LocE F E) (ψ : (F × F) ≃ₗ[F] E) :
    ∃ h : (F × F) ≃ₜ E, ∀ p, h p = ψ p := by
  have := L.top
  have := IsModuleTopology.toContinuousAdd F E
  exact ⟨{ toEquiv := ψ.toEquiv
           continuous_toFun := IsModuleTopology.continuous_of_linearMap ψ.toLinearMap
           continuous_invFun := IsModuleTopology.continuous_of_linearMap ψ.symm.toLinearMap }, fun _ => rfl⟩
end GlobalTheory.SgLoc.Top
