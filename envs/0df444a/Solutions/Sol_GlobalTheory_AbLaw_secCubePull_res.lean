-- Prove2me | solution 1 for GlobalTheory.AbLaw.secCubePull_res
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:48:04.679138+00:00
-- url     : https://prove2.me/submissions/fcd49785-955a-4a13-8bce-0a84217bd3a3

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoTermComparisonRestrictScalars
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_BijectiveSmulChartSec
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Theorems.Thm_GlobalTheory_AbLaw_SecOn_pull_restrict
import Theorems.Thm_GlobalTheory_AbLaw_SecOnR_pull_restrict

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.AbLaw
variable {X X' : Scheme.{0}} {R R' : Type} [CommRing R] [CommRing R']
variable {κ : Type} (f : X ⟶ Spec (CommRingCat.of R)) {L : LB X} (M : LB X) (D : κ → X.Opens)
variable {M}
variable {f} {f' : X' ⟶ Spec (CommRingCat.of R')} {π : X' ⟶ X} {g : R →+* R'}
  (w : π ≫ f = f' ≫ Spec.map (CommRingCat.ofHom g))
namespace GlobalTheory.AbLaw
theorem _root_.solution {s t : Finset κ} (h : s ⊆ t) (x : (secCube f M D).obj s) :
    secCubePull M D w t (GlobalTheory.Cube.res (secCube f M D) h x) =
      GlobalTheory.Cube.res (secCube f' (M.pull π) fun i => π ⁻¹ᵁ D i) h (secCubePull M D w s x) :=
  SecOnR.pull_restrict w (iInf_le_iInf_of_subset D h)
    (iInf_le_iInf_of_subset (fun i => π ⁻¹ᵁ D i) h) (preimage_biInf D π s).ge
    (preimage_biInf D π t).ge x
end GlobalTheory.AbLaw
