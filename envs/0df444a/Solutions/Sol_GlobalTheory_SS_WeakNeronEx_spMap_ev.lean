-- Prove2me | solution 1 for GlobalTheory.SS.WeakNeronEx.spMap_ev
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:21:59.94186+00:00
-- url     : https://prove2.me/submissions/bbeb2946-7f54-468a-9119-da26a7f7a05a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SmoothFlatAlgebraFiniteCoverDecompStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsSchemeModelOfAffineSmoothChartStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsCoverModelIrreducibleSpecialFibreStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsWeakNeronModel

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
set_option backward.isDefEq.respectTransparency false
noncomputable section
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.WeakNeronEx
open GlobalTheory.AbLaw ReciprocityTheory.ChartRestriction.G.Out
variable {X : Scheme.{0}} {L : Type} [Field L] (a : Sp L ⟶ X)
namespace GlobalTheory.SS.WeakNeronEx
theorem _root_.solution {W : X.Opens} (hW : IsAffineOpen W) (h : ⊤ ≤ a ⁻¹ᵁ W) :
    spMap (ev a W h) ≫ hW.fromSpec = a := by
  have e := IsAffineOpen.SpecMap_appLE_fromSpec a hW (isAffineOpen_top _) h
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at e
  have : spMap (ev a W h) = Spec.map (Scheme.ΓSpecIso (CommRingCat.of L)).hom ≫ Spec.map (a.appLE W ⊤ h) :=
    Spec.map_comp (a.appLE W ⊤ h) _
  rw [this, Category.assoc, e, ← Category.assoc, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id,
    Category.id_comp]
end GlobalTheory.SS.WeakNeronEx
