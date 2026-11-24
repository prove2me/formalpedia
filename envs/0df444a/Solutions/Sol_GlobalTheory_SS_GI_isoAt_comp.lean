-- Prove2me | solution 1 for GlobalTheory.SS.GI.isoAt_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:16:42.269429+00:00
-- url     : https://prove2.me/submissions/9618ada6-58a6-4a53-b5ee-038c86e9d1c5

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsLiftOfSchemeTheoreticallyDominant
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ModelMapGenericallyOpenImmersionCalculus
import Theorems.Thm_GlobalTheory_SS_GI_isoAt_iff
import Theorems.Thm_GlobalTheory_SS_GI_Via_comp_pullback

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
theorem _root_.solution {M : Model R A} {N : Model R A'} {P : Model R A''} {f : A ⟶ A'} {f' : A' ⟶ A''}
    {W : Scheme.{0}} {u : W ⟶ M.Y.left} [IsOpenImmersion u] {g : W ⟶ N.Y.left} [IsOpenImmersion g]
    (h : Via M N f u g) (w : W) (h' : IsoAt N P f' (g w)) : IsoAt M P (f ≫ f') (u w) := by
  replace h' := isoAt_iff.1 h'
  obtain ⟨W', u', g', w', _, _, e, h'⟩ := h'
  obtain ⟨z, rfl, rfl⟩ := Scheme.Pullback.exists_preimage_pullback (f := g) (g := u') w w' e.symm
  exact isoAt_iff.2 ⟨_, _, _, z, inferInstance, inferInstance, Scheme.Hom.comp_apply _ _ _, h.comp_pullback h'⟩
end GlobalTheory.SS.GI
