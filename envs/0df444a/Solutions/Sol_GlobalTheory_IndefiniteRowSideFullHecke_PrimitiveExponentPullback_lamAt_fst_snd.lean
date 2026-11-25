-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.PrimitiveExponentPullback.lamAt_fst_snd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:51:50.004265+00:00
-- url     : https://prove2.me/submissions/7095caaf-97d3-4e24-acb9-bbde3d4a6da2

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_AbelianSchemeQuotients_IsAbelianScheme
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_CubicalStructures_CubicalPullBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_HostConjugateIdeal
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_PrimitiveExponentPullback

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField AlgebraicGeometry CategoryTheory Limits MonoidalCategory
  CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.PrimitiveExponentPullback
open GlobalTheory.IndefiniteRowSideFullHecke.HostConjugateIdeal
variable {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G]
namespace GlobalTheory.IndefiniteRowSideFullHecke.PrimitiveExponentPullback
theorem _root_.solution (L : LB G.left) : lamAt G L (fst G G) (snd G G) = abelian₂ G L := rfl
end GlobalTheory.IndefiniteRowSideFullHecke.PrimitiveExponentPullback
