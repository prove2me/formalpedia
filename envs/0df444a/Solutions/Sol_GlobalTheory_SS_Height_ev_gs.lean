-- Prove2me | solution 1 for GlobalTheory.SS.Height.ev_gs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:18:00.520705+00:00
-- url     : https://prove2.me/submissions/fc7d1d95-a7d1-4a6e-b7ec-975d5ffd147a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsUniquePointOfRingHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsLineBundleHeightProperScheme

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
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.Height
open IsLocalRing
namespace GlobalTheory.SS.Height
theorem _root_.solution {R : Type} [CommRing R] [IsLocalRing R] {X : Scheme.{0}} (b : Sp R ⟶ X) (U : X.Opens)
    (h : b (closedPoint R) ∈ U) (h' : ⊤ ≤ b ⁻¹ᵁ U) (f : Γ(X, U)) :
    ev R (gs b (closedPoint R) U f) = (b.appLE U ⊤ h' ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom).hom f := by
  rw [gs_eq b _ U h, ← germ_stalkClosedPointIso_hom]
  simp only [Scheme.Hom.appLE, CommRingCat.hom_comp, RingHom.comp_apply, ev]
  congr 1
  exact (TopCat.Presheaf.germ_res_apply (Sp R).presheaf (homOfLE h') (closedPoint R) (Set.mem_univ _) _).symm
end GlobalTheory.SS.Height
