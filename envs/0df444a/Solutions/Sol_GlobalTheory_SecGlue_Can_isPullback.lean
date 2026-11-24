-- Prove2me | solution 1 for GlobalTheory.SecGlue.Can.isPullback
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:35:55.393233+00:00
-- url     : https://prove2.me/submissions/0d1f9f15-a650-4303-bc44-87967dd099e0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_UnivFrame
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AllTest
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsUniqueGlueSectionsPrincipalCover

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames
open TopologicalSpace
open GlobalTheory GlobalTheory.SecGlue
variable {B : Scheme.{0}} (G : Over B) {S T : Scheme.{0}}
variable {G}
namespace GlobalTheory.SecGlue
namespace Can
theorem _root_.solution {f : T ⟶ S} {x : S ⟶ B} {x' : T ⟶ B} (e : f ≫ x = x') {pm}
    (h : Can G f x x' pm) :
    IsPullback pm (fst (Over.mk x') G).left (fst (Over.mk x) G).left f := by
  have h1 : IsPullback (snd (Over.mk x) G).left (fst (Over.mk x) G).left G.hom x :=
    (IsPullback.of_hasPullback x G.hom).flip
  have h2 : IsPullback (snd (Over.mk x') G).left (fst (Over.mk x') G).left G.hom x' :=
    (IsPullback.of_hasPullback x' G.hom).flip
  refine IsPullback.of_right ?_ h.2 h1
  rw [h.1]
  exact e ▸ h2
end Can
end GlobalTheory.SecGlue
