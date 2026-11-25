-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.CubicalPullbackLaw.CubicalPullLaw.ofHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:51:34.7279+00:00
-- url     : https://prove2.me/submissions/0b9e31fa-5b4d-41f5-9c13-1275bd7ac07b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_AbelianSchemeQuotients_QSurjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_CubicalStructures_CubicalPullBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_AbelianSchemeLaw_CubicalPullbackLaw

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.CubicalPullbackLaw
namespace GlobalTheory.IndefiniteRowSideFullHecke.CubicalPullbackLaw
namespace CubicalPullLaw
theorem _root_.solution (h : CubicalPullLaw) : CubicalPullOfHomSt.{0} := by
  intro S G' G _ _ _ _ f _ L c
  obtain ⟨hL, hr, c', hc, _⟩ := h (CubeMap.ofHom f) L c
  exact ⟨hL, hr, c', hc⟩
end CubicalPullLaw
end GlobalTheory.IndefiniteRowSideFullHecke.CubicalPullbackLaw
