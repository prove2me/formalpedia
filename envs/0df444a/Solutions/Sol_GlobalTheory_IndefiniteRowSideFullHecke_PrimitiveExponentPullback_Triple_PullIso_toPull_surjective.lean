-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.PrimitiveExponentPullback.Triple.PullIso.toPull_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:51:39.912106+00:00
-- url     : https://prove2.me/submissions/e707f89d-6b91-4444-872f-ca2d5d637f59

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
namespace PullIso
theorem _root_.solution {t' : Triple H S'} {t : Triple H S} {f : S' ⟶ S} :
    Function.Surjective (PullIso.toPull (t' := t') (t := t) (f := f)) := by
  rintro ⟨φ, h1, h2, m, rfl, h3, w, h4, h5, h6⟩
  exact ⟨⟨m, h3, h1, h2, w, h4, h5, h6⟩, rfl⟩
end PullIso
end GlobalTheory.IndefiniteRowSideFullHecke.PrimitiveExponentPullback.Triple
