-- Prove2me | solution 1 for GlobalTheory.ExtUnique.dense_open
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:02:04.242121+00:00
-- url     : https://prove2.me/submissions/eaa17e2e-f172-4442-b2ea-e1fa243c2f65

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
theorem _root_.solution {S : Scheme.{u}} [IsReduced S] [IsLocallyNoetherian S] (U : S.Opens)
    (hU : Dense (U : Set S)) : QuasiCompact U.ι ∧ IsSchemeTheoreticallyDominant U.ι := by
  have := Opens.isDominant_ι (X := S) hU
  exact ⟨inferInstance, .of_isDominant _⟩
end GlobalTheory.ExtUnique
