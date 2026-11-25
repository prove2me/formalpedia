-- Prove2me | solution 1 for GlobalTheory.SS.GI.Via.apply_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:22:04.374197+00:00
-- url     : https://prove2.me/submissions/227ca32d-24fb-4e3f-8c3a-d18995bb440b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsLiftOfSchemeTheoreticallyDominant
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ModelMapGenericallyOpenImmersionCalculus
import Theorems.Thm_GlobalTheory_SS_GI_Via_unique

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
namespace Via
theorem _root_.solution [IsDomain R] [IsFractionRing R K] {M : Model R A} {N : Model R A'} {f : A ⟶ A'}
    {W W' : Scheme.{0}} {u : W ⟶ M.Y.left} {u' : W' ⟶ M.Y.left} [Flat u] [Flat u']
    {g : W ⟶ N.Y.left} {g' : W' ⟶ N.Y.left} (h : Via M N f u g) (h' : Via M N f u' g')
    {w : W} {w' : W'} (e : u w = u' w') : g w = g' w' := by
  obtain ⟨z, rfl, rfl⟩ := Scheme.Pullback.exists_preimage_pullback (f := u) (g := u') w w' e
  have h2 := h'.precomp (pullback.snd u u')
  rw [← pullback.condition] at h2
  have := (h.precomp (pullback.fst u u')).unique h2
  rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, this]
end Via
end GlobalTheory.SS.GI
