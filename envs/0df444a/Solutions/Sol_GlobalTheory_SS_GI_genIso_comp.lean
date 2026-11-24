-- Prove2me | solution 1 for GlobalTheory.SS.GI.genIso_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:56:04.667804+00:00
-- url     : https://prove2.me/submissions/e985a726-28f3-489c-bcb7-478fdcac66a9

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsLiftOfSchemeTheoreticallyDominant
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ModelMapGenericallyOpenImmersionCalculus
import Theorems.Thm_GlobalTheory_SS_GI_isoAt_iff
import Theorems.Thm_GlobalTheory_SS_GI_isOpen_isoAt
import Theorems.Thm_GlobalTheory_SS_GI_Via_mem_sp
import Theorems.Thm_GlobalTheory_SS_GI_isoAt_comp

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
variable [IsLocalRing R]
namespace GlobalTheory.SS.GI
theorem _root_.solution {M : Model R A} {N : Model R A'} {P : Model R A''} {f : A ⟶ A'} {f' : A' ⟶ A''}
    (hN : N.Irr) (h : GenIso M N f) (h' : GenIso N P f') : GenIso M P (f ≫ f') := by
  obtain ⟨y, hy, h⟩ := h
  replace h := isoAt_iff.1 h
  obtain ⟨W, u, g, w, _, _, rfl, h⟩ := h
  obtain ⟨_, hz, ⟨w', rfl⟩, hz'⟩ := hN.2 _ _ g.opensRange.isOpen (isOpen_isoAt N P f')
    ⟨g w, (h.mem_sp w).2 hy, w, rfl⟩ h'
  exact ⟨u w', (h.mem_sp w').1 hz, isoAt_comp h w' hz'⟩
end GlobalTheory.SS.GI
