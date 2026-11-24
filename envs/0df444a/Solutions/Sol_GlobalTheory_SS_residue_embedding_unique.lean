-- Prove2me | solution 1 for GlobalTheory.SS.residue_embedding_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:24:42.463532+00:00
-- url     : https://prove2.me/submissions/9d1227fc-8147-4752-be6a-856e24a10279

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsFieldOfValues

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
open GlobalTheory GlobalTheory.SS
namespace GlobalTheory.SS
theorem _root_.solution {X : Scheme.{0}} {Ω : CommRingCat.{0}} [Nonempty (Spec Ω)]
    {p q : X} (φ : X.residueField p ⟶ Ω) (ψ : X.residueField q ⟶ Ω)
    (h : Spec.map φ ≫ X.fromSpecResidueField p = Spec.map ψ ≫ X.fromSpecResidueField q) :
    ∃ e : p = q, φ = (X.residueFieldCongr e).hom ≫ ψ := by
  obtain ⟨t⟩ := ‹Nonempty (Spec Ω)›
  have e : p = q := by
    have := congrArg (fun f => f t) h
    simpa only [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply] using this
  subst e
  refine ⟨rfl, ?_⟩
  rw [cancel_mono, Spec.map_inj] at h
  simpa using h
end GlobalTheory.SS
