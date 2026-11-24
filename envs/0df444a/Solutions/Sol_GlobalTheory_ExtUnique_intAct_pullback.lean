-- Prove2me | solution 1 for GlobalTheory.ExtUnique.intAct_pullback
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:49:24.538928+00:00
-- url     : https://prove2.me/submissions/341a7d77-ebaa-4e24-8701-e00db0cc424c

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
variable {U S : Scheme.{0}} {j : U ⟶ S} [QuasiCompact j] [IsSchemeTheoreticallyDominant j]
namespace GlobalTheory.ExtUnique
theorem _root_.solution {U S : Scheme.{0}} (j : U ⟶ S) (G : Over S) [GrpObj G] [IsCommMonObj G] (n : ℤ) :
    (Over.pullback j).map ((intAct G).act n) = (intAct ((Over.pullback j).obj G)).act n := by
  have h := map_zpow (MonoidHom.mk' (fun f : G ⟶ G => (Over.pullback j).map f)
    fun _ _ => CategoryTheory.Functor.map_mul _ _ _) (𝟙 G) n
  simpa [intAct] using h
end GlobalTheory.ExtUnique
