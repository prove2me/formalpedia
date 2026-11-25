-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.PrimitiveExponentPullback.Triple.cubeMap_tripleProduct_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:51:45.296361+00:00
-- url     : https://prove2.me/submissions/ef5f2085-7d33-4cbd-839e-e0286f3597c6

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_AbelianSchemeQuotients_IsAbelianScheme
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_CubicalStructures_CubicalPullBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_HostConjugateIdeal
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_PrimitiveExponentPullback
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_PrimitiveExponentPullback_Triple_cubeMap_coord
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_HostConjugateIdeal_Level_Dvd_trans


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
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
attribute [instance] Triple.grp Triple.comm
open GlobalTheory.IndefiniteRowSideFullHecke.PrimitiveExponentPullback.Triple
variable {H : Host E} {S S' : Scheme.{0}}
namespace GlobalTheory.IndefiniteRowSideFullHecke.PrimitiveExponentPullback.Triple
theorem _root_.solution {G' : Over S'} {G : Over S} [GrpObj G'] [IsCommMonObj G'] [GrpObj G]
    [IsCommMonObj G] (m m' : CubeMap G' G) (h : m.F = m'.F) : m.F3 = m'.F3 := by
  have h0 := (cubeMap_coord m 0).trans (h ▸ (cubeMap_coord m' 0).symm)
  have h1 := (cubeMap_coord m 1).trans (h ▸ (cubeMap_coord m' 1).symm)
  have h2 := (cubeMap_coord m 2).trans (h ▸ (cubeMap_coord m' 2).symm)
  apply pullback.hom_ext
  · exact h0
  · apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc]; exact h1
    · rw [Category.assoc, Category.assoc]; exact h2
end GlobalTheory.IndefiniteRowSideFullHecke.PrimitiveExponentPullback.Triple
