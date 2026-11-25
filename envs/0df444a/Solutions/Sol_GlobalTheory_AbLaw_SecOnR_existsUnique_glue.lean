-- Prove2me | solution 1 for GlobalTheory.AbLaw.SecOnR.existsUnique_glue
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:56:45.357811+00:00
-- url     : https://prove2.me/submissions/f12d8b97-3211-49cb-917b-6cc70259c9fb

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoTermComparisonRestrictScalars
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_BijectiveSmulChartSec
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Theorems.Thm_GlobalTheory_AbLaw_SecOn_existsUnique_glue

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
open GlobalTheory.AbLaw.SecOnR
variable (f : X ⟶ Spec (CommRingCat.of R)) {L M H : LB X} {V W : X.Opens}
variable {f}
variable (f)
namespace GlobalTheory.AbLaw.SecOnR
theorem _root_.solution {I : Type} (O : I → X.Opens) (hO : ∀ a, O a ≤ V) (hc : V ≤ ⨆ a, O a)
    (s : ∀ a, SecOnR f M (O a))
    (h : ∀ a b, restrict f M (inf_le_left : O a ⊓ O b ≤ O a) (s a) =
      restrict f M (inf_le_right : O a ⊓ O b ≤ O b) (s b)) :
    ∃! t : SecOnR f M V, ∀ a, restrict f M (hO a) t = s a :=
  SecOn.existsUnique_glue O hO hc s h
end GlobalTheory.AbLaw.SecOnR
