-- Prove2me | solution 1 for GlobalTheory.SS.WtRat.ev_spMap_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:22:05.111119+00:00
-- url     : https://prove2.me/submissions/c46e1705-980c-46a9-a221-e4b4dd0bfea8

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_IsUnitEv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsFractionEvalSectionAffineNearPoint
import Theorems.Thm_GlobalTheory_SS_WtRat_ev_top


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
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.WtRat
namespace GlobalTheory.SS.WtRat
theorem _root_.solution {R F : Type} [CommRing R] [CommRing F] (e : R →+* F)
    (h : ⊤ ≤ spMap e ⁻¹ᵁ ⊤) (u : Γ(Sp R, ⊤)) :
    ev (spMap e) ⊤ h u = e ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom u) :=
  (ev_top (spMap e) h u).trans
    (congrArg (fun q => CommRingCat.Hom.hom q u)
      (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom e)))
end GlobalTheory.SS.WtRat
