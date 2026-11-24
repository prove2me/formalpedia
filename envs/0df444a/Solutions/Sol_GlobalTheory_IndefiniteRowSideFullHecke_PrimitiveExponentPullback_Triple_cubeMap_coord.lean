-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.PrimitiveExponentPullback.Triple.cubeMap_coord
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:40:24.444893+00:00
-- url     : https://prove2.me/submissions/247e6cfb-7ed1-45ff-92dd-39bc96a70ec1

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
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
attribute [instance] Triple.grp Triple.comm
open GlobalTheory.IndefiniteRowSideFullHecke.PrimitiveExponentPullback.Triple
variable {H : Host E} {S S' : Scheme.{0}}
namespace GlobalTheory.IndefiniteRowSideFullHecke.PrimitiveExponentPullback.Triple
theorem _root_.solution {G' : Over S'} {G : Over S} [GrpObj G'] [IsCommMonObj G'] [GrpObj G]
    [IsCommMonObj G] (m : CubeMap G' G) (i : Fin 3) :
    m.F3 ≫ (x3 G i).left = (x3 G' i).left ≫ m.F := by
  have h := m.psum_comm {i}
  have e : psum G (x3 G) {i} = x3 G i := by
    fin_cases i <;> exact _root_.mul_one (M := G3 G ⟶ G) _
  have e' : psum G' (x3 G') {i} = x3 G' i := by
    fin_cases i <;> exact _root_.mul_one (M := G3 G' ⟶ G') _
  rw [e, e'] at h
  exact h.symm
end GlobalTheory.IndefiniteRowSideFullHecke.PrimitiveExponentPullback.Triple
