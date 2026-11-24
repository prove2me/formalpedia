-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.PrimitiveExponentPullback.lamPt_values
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:40:25.650373+00:00
-- url     : https://prove2.me/submissions/db6c439c-56ff-49df-851b-ccf284da74f1

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
theorem _root_.solution {T : Over S} (x z : T ⟶ G) :
    lamPt G x z ⟨∅⟩ = (1 : T ⟶ G).left ∧ lamPt G x z ⟨{0}⟩ = x.left ∧
      lamPt G x z ⟨{1}⟩ = z.left ∧ lamPt G x z ⟨{0, 1}⟩ = (x * z).left := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · change (x * 1).left = _
    rw [_root_.mul_one]
  · change (z * 1).left = _
    rw [_root_.mul_one]
  · change (x * (z * 1)).left = _
    rw [_root_.mul_one]
end GlobalTheory.IndefiniteRowSideFullHecke.PrimitiveExponentPullback
