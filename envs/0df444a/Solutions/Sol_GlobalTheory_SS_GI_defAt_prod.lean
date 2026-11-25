-- Prove2me | solution 1 for GlobalTheory.SS.GI.defAt_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:13:33.320458+00:00
-- url     : https://prove2.me/submissions/76033355-0707-4f63-8506-89e83d929568

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsLiftOfSchemeTheoreticallyDominant
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ModelMapGenericallyOpenImmersionCalculus
import Theorems.Thm_GlobalTheory_SS_GI_defAt_iff
import Theorems.Thm_GlobalTheory_SS_GI_exists_prodMap_apply

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
theorem _root_.solution {M : Model R A} {N : Model R A'} {P : Model R B} {Q : Model R B'} {f : A ⟶ B} {f' : A' ⟶ B'}
    {z : (M.prod N).Y.left} (h : DefAt M P f ((fst M.Y N.Y).left z)) (h' : DefAt N Q f' ((snd M.Y N.Y).left z)) :
    DefAt (M.prod N) (P.prod Q) (f ⊗ₘ f') z := by
  obtain ⟨W, u, g, w, _, e, h⟩ := defAt_iff.1 h
  obtain ⟨W', u', g', w', _, e', h'⟩ := defAt_iff.1 h'
  obtain ⟨t, ht⟩ := exists_prodMap_apply u u' z w w' e e'
  exact defAt_iff.2 ⟨_, _, _, t, inferInstance, ht, h.prod h'⟩
end GlobalTheory.SS.GI
