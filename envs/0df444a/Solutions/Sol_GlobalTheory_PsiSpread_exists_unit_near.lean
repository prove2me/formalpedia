-- Prove2me | solution 1 for GlobalTheory.PsiSpread.exists_unit_near
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:52:14.776375+00:00
-- url     : https://prove2.me/submissions/f3fe7c10-6712-449e-a209-90e8a52bbf5c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TauBimultOfIsPullDeg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsFiniteCubeInduction
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory
open GlobalTheory.PsiSpread
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
namespace GlobalTheory.PsiSpread
theorem _root_.solution {X Y : Scheme.{0}} (f : Y ⟶ X) [IsPreimmersion f] (y : Y) (a : (Y.presheaf.stalk y)ˣ) :
    ∃ (U : X.Opens) (u : Γ(X, U)ˣ), f y ∈ U ∧ gm f y U u = a := by
  obtain ⟨s, hs⟩ := f.stalkMap_surjective y a.val
  obtain ⟨U, hU, g, rfl⟩ := X.presheaf.exists_germ_eq s
  have hu : IsUnit ((X.presheaf.germ U (f y) hU).hom g) :=
    (isUnit_map_iff (f.stalkMap y).hom _).1 (hs ▸ a.isUnit)
  have hm : f y ∈ X.basicOpen g := (X.mem_basicOpen g (f y) hU).2 hu
  refine ⟨X.basicOpen g, (X.toRingedSpace.isUnit_res_basicOpen g).unit, hm, Units.ext ?_⟩
  refine (gs_unit f y _ hm _).symm.trans ((gs_res f y (X.basicOpen_le g) hm g).trans ((gs_eq f y U hU g).trans ?_))
  exact (Scheme.Hom.germ_stalkMap_apply f U y hU g).symm.trans hs
end GlobalTheory.PsiSpread
