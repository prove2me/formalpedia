-- Prove2me | solution 1 for GlobalTheory.SS.GI.isoAt_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:54:31.018095+00:00
-- url     : https://prove2.me/submissions/f9486d8c-582d-43c3-8f6c-c697fc4284cc

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsLiftOfSchemeTheoreticallyDominant
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ModelMapGenericallyOpenImmersionCalculus
import Theorems.Thm_GlobalTheory_SS_GI_extends_iff_via

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
noncomputable section
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.GI
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] {K : Type} [Field K] [Algebra R K] {A A' A'' B B' : Over (Sp K)}
namespace GlobalTheory.SS.GI
theorem _root_.solution {M : Model R A} {N : Model R A'} {f : A ⟶ A'} {y : M.Y.left} :
    IsoAt M N f y ↔ ∃ (W : Scheme.{0}) (u : W ⟶ M.Y.left) (g : W ⟶ N.Y.left) (w : W),
      IsOpenImmersion u ∧ IsOpenImmersion g ∧ u w = y ∧ Via M N f u g := by
  constructor
  · rintro ⟨U, g, hy, h, hg⟩
    exact ⟨_, U.ι, g, ⟨y, hy⟩, inferInstance, hg, rfl, extends_iff_via.1 h⟩
  · rintro ⟨W, u, g, w, _, _, rfl, h⟩
    refine ⟨u.opensRange, u.isoOpensRange.inv ≫ g, ⟨w, rfl⟩, extends_iff_via.2 ?_, inferInstance⟩
    simpa using h.precomp u.isoOpensRange.inv
end GlobalTheory.SS.GI
