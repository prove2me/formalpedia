-- Prove2me | solution 1 for GlobalTheory.ZJ.AddExt.isPullback_a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:21:34.7874+00:00
-- url     : https://prove2.me/submissions/8e34b7c9-774b-4701-9916-b1d9569a5b9d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_IsNormalSchemeSp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FiniteOfIsClosedOfFiniteInterClosedPoints
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsAddExtension

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ
open GlobalTheory GlobalTheory.ZJ GlobalTheory.ZJ.AddExt
namespace GlobalTheory.ZJ.AddExt
theorem _root_.solution (C : Core) : IsPullback C.a C.A.hom C.GG.hom C.U.ι := by
  refine ⟨⟨by simpa using C.cart.w⟩, ⟨PullbackCone.IsLimit.mk _
    (fun s => C.cart.lift (s.fst ≫ C.G.ι) s.snd (by simpa using s.condition)) (fun s => ?_) (fun s => ?_)
    (fun s m h1 h2 => ?_)⟩⟩
  · rw [← cancel_mono C.G.ι, Category.assoc, IsPullback.lift_fst]
  · rw [IsPullback.lift_snd]
  · apply C.cart.hom_ext
    · rw [IsPullback.lift_fst, ← h1, Category.assoc]
    · rw [IsPullback.lift_snd, h2]
end GlobalTheory.ZJ.AddExt
