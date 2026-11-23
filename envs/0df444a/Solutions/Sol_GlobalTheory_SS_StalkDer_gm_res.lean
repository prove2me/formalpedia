-- Prove2me | solution 1 for GlobalTheory.SS.StalkDer.gm_res
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:50:31.78683+00:00
-- url     : https://prove2.me/submissions/d3c023e9-78eb-4662-8722-e8463bc90383

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsStalkDerivationOfIsPullback
import Theorems.Thm_GlobalTheory_SS_StalkDer_germ_appLE

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
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.StalkDer
variable {K : Type} [Field K] {P : Scheme.{0}} {X : Over (Sp K)}
namespace GlobalTheory.SS.StalkDer
theorem _root_.solution (f : P ⟶ X.left) (z : P) (V V' : X.left.Opens) (h : V' ≤ V) (hz : z ∈ f ⁻¹ᵁ V')
    (u : Γ(X.left, V)) :
    gm f z V' hz ((X.left.presheaf.map (homOfLE h).op).hom u) = gm f z V (h hz) u := by
  rw [← germ_appLE f z V' _ le_rfl hz, ← germ_appLE f z V (f ⁻¹ᵁ V') (fun _ hx => h hx) hz]
  congr 1
  exact congrArg (fun φ => φ.hom u) (f.map_appLE le_rfl (homOfLE h).op)
end GlobalTheory.SS.StalkDer
