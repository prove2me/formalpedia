-- Prove2me | solution 1 for GlobalTheory.SS.WeakNeronEx.ev_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:24:38.676869+00:00
-- url     : https://prove2.me/submissions/ccf02494-8564-4794-afe3-ff6dc421a82a

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
theorem _root_.solution {W : X.Opens} (h : ⊤ ≤ a ⁻¹ᵁ W) (f : Γ(X, W)) :
    ev a W h f ≠ 0 ↔ ⊤ ≤ a ⁻¹ᵁ X.basicOpen f := by
  have e := Scheme.basicOpen_appLE a ⊤ W h f
  rw [top_inf_eq] at e
  rw [← e, ← isUnit_iff_ne_zero]
  constructor
  · intro hu
    have : IsUnit ((a.appLE W ⊤ h).hom f) := by
      have := hu.map (Scheme.ΓSpecIso (CommRingCat.of L)).inv.hom
      simpa [ev] using this
    exact (Scheme.basicOpen_of_isUnit _ this).ge
  · intro hu
    have : IsUnit ((a.appLE W ⊤ h).hom f) :=
      RingedSpace.isUnit_of_isUnit_germ (Sp L).toRingedSpace ⊤ _ fun x hx =>
        (Scheme.mem_basicOpen _ _ x hx).1 (hu hx)
    exact this.map (Scheme.ΓSpecIso (CommRingCat.of L)).hom.hom
end GlobalTheory.SS.WeakNeronEx
