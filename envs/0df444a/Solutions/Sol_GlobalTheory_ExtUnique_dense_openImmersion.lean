-- Prove2me | solution 1 for GlobalTheory.ExtUnique.dense_openImmersion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:49:22.96429+00:00
-- url     : https://prove2.me/submissions/827526ec-427b-48e8-885b-d8299d080e7a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsSchemeTheoreticallyDominantSpecMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsSchemeTheoreticallyDominantSpecOfInjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
universe u
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.ExtUnique
namespace GlobalTheory.ExtUnique
theorem _root_.solution {U S : Scheme.{u}} [IsReduced S] [IsLocallyNoetherian S] (j : U ⟶ S)
    [IsOpenImmersion j] [IsDominant j] : QuasiCompact j ∧ IsSchemeTheoreticallyDominant j :=
  ⟨inferInstance, .of_isDominant _⟩
end GlobalTheory.ExtUnique
